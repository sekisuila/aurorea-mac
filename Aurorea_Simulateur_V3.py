#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""AUROREA - Simulateur statistique tout-en-un V3 avec interface Windows.

Un SEUL fichier Python contient : règles expérimentales, simulation, CSV,
comparaisons des stratégies, graphiques et génération du rapport PDF.

Installation (une seule fois) :
    py -m pip install matplotlib numpy reportlab

Démarrage avec fenêtre :
    py Aurorea_Tout_En_Un.py

Test sans interface (fonctionne aussi sous Linux) :
    python Aurorea_Tout_En_Un.py --simuler --parties 12 --out mon_dossier
    python Aurorea_Tout_En_Un.py --rapport mon_dossier/experience_...

Le moteur est une MODÉLISATION EXPLORATOIRE des règles du 30 octobre,
pas une intelligence artificielle maîtrisant parfaitement Aurorea.
La graine 0 signifie : tirer une nouvelle graine et enregistrer sa valeur.
Le tableau final ventile les points par origine, clan et stratégie.
La version courte utilise 4 saisons et la longue 8 saisons ; les variantes
sont celles de l'étude v2, y compris les simplifications des événements.

Les résultats sont reproductibles si la graine et les réglages restent identiques.
Le rapport signale explicitement les incertitudes et les échantillons réduits.
"""
from __future__ import annotations

# Bibliothèque standard : aucun autre fichier Python du projet n'est nécessaire.
import argparse
import collections
import csv
import html
import json
import math
import os
import random
import secrets  # Une graine automatique provient du générateur sécurisé du système.
import statistics
import sys
import threading
import tkinter as tk
import traceback
import xml.sax.saxutils as saxutils
from collections import defaultdict
from copy import deepcopy
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from tkinter import ttk, messagebox, filedialog

# Le programme recherche ses ressources par rapport à son propre emplacement.
HOME = Path(__file__).resolve().parent


# ========= PARAMÈTRES DES HUIT CLANS =========
CLAN_DEFAULTS = {
 'cerf':dict(deplacement=3, dispersion_libre=False, bonus_ressource='flint',bonus_quantite=1,
             bois_bonus_automne_hiver=1, nourriture_foret_printemps_ete=1,
             surcout_hutte_bois=0,surcout_hutte_os=1, vitesse_malus_hiver=1),
 'serpent':dict(deplacement=1, dispersion_libre=True, bonus_ressource='flint',bonus_quantite=1,
             immunite_blessure=True, immunite_evenements_nourriture=True,
             niveau_chamane_depart=2, nourriture_supplementaire_saison=1),
 'ours':dict(deplacement=2,dispersion_libre=False,bonus_ressource='flint',bonus_quantite=1,
             immunite_evenements_attaque=True, pas_de_peau_saison=True,
             nourriture_supplementaire_automne=1,nourriture_supplementaire_hiver=1,
             sans_nomades=True),
 'aigle':dict(deplacement=2,dispersion_libre=False,bonus_ressource='flint',bonus_quantite=1,
             consultation_deux_tuiles=True,choix_deux_evenements=True,surcout_hutte_bois=1),
 'loup':dict(deplacement=3,dispersion_libre=False,bonus_ressource='wood',bonus_quantite=1,
             os_bonus_chasse=1,nourriture_bonus_chasse_groupe=1,
             nourriture_supplementaire_hiver=1),
 'sanglier':dict(deplacement=2,dispersion_libre=False,bonus_ressource='wood',bonus_quantite=1,
             plante_bonus_plaine_foret=1,choix_deux_evenements=True,
             nourriture_supplementaire_hiver=1,surcout_hutte_os=1),
 'saumon':dict(deplacement=2,dispersion_libre=False,bonus_ressource='water',bonus_quantite=1,
             nourriture_bonus_tuile_eau=1,immunite_evenements_eau=True,
             eau_supplementaire_saison=1,interdit_desert=True),
 'castor':dict(deplacement=1,dispersion_libre=True,bonus_ressource='water',bonus_quantite=1,
             nourriture_bonus_riviere=1, hutte_immunisee=True,
             chasse_grande_accompagnateurs=2,eau_cout_desert=1,
             cout_hutte_castor_deux_bois=True)
}
# Tous les champs disponibles existent pour chaque clan : la GUI peut donc les modifier.
DEFAULT_CLAN_FIELDS = dict(
    deplacement=1, dispersion_libre=False,bonus_ressource='wood',bonus_quantite=0,
    bois_bonus_automne_hiver=0,nourriture_foret_printemps_ete=0,
    surcout_hutte_bois=0,surcout_hutte_os=0,vitesse_malus_hiver=0,
    immunite_blessure=False,immunite_evenements_nourriture=False,
    immunite_evenements_eau=False,immunite_evenements_attaque=False,
    niveau_chamane_depart=1,nourriture_supplementaire_saison=0,
    nourriture_supplementaire_automne=0,nourriture_supplementaire_hiver=0,
    eau_supplementaire_saison=0,pas_de_peau_saison=False,sans_nomades=False,
    consultation_deux_tuiles=False,choix_deux_evenements=False,
    os_bonus_chasse=0,nourriture_bonus_chasse_groupe=0,
    plante_bonus_plaine_foret=0,nourriture_bonus_tuile_eau=0,
    nourriture_bonus_riviere=0,hutte_immunisee=False,
    chasse_grande_accompagnateurs=1,eau_cout_desert=0,
    interdit_desert=False,cout_hutte_castor_deux_bois=False,
)

def configuration_defaut():
    """Construit un dictionnaire indépendant, prêt à sauver dans un JSON."""
    return dict(simulation=dict(parties=1000,graine=0,saisons=[4,8],
              avec_evenements=[False,True],points_par_troc=1,
              maximum_points_troc_par_saison=1,maximum_offres_par_tour=2,
              probabilite_troc_aleatoire=0.5),
              clans={name:{**deepcopy(DEFAULT_CLAN_FIELDS),**mods} for name,mods in CLAN_DEFAULTS.items()})

def charger_configuration(chemin):
    """Charge le fichier JSON et vérifie avant toute simulation."""
    data=json.loads(Path(chemin).read_text(encoding='utf-8'))
    valider_configuration(data)
    return data

def valider_configuration(data):
    """Évite les erreurs courantes de paramètres avant les calculs."""
    if not isinstance(data,dict) or 'simulation' not in data or 'clans' not in data:
        raise ValueError('Le JSON doit contenir « simulation » et « clans ».')
    sim=data['simulation']
    if not isinstance(sim['parties'],int) or not 1<=sim['parties']<=100000:
        raise ValueError('parties doit être un entier entre 1 et 100000.')
    if not isinstance(sim['graine'],int):
        raise ValueError('graine doit être un entier.')
    if not set(sim['saisons']).issubset({4,8}) or not sim['saisons']:
        raise ValueError('saisons doit être une liste contenant 4 et/ou 8.')
    if not sim['avec_evenements'] or any(type(x)!=bool for x in sim['avec_evenements']):
        raise ValueError('avec_evenements doit contenir true et/ou false.')
    for k in ['points_par_troc','maximum_points_troc_par_saison','maximum_offres_par_tour']:
        if not isinstance(sim[k],int) or not 0<=sim[k]<=100:
            raise ValueError(f'{k} doit être un entier entre 0 et 100.')
    if not 0<=sim['probabilite_troc_aleatoire']<=1:
        raise ValueError('La probabilité doit être comprise entre 0 et 1.')
    if set(data['clans'])!=set(CLAN_DEFAULTS):
        raise ValueError('Le fichier doit décrire les huit clans officiels.')
    for nom,cfg in data['clans'].items():
        if set(cfg)!=set(DEFAULT_CLAN_FIELDS):
            missing=set(DEFAULT_CLAN_FIELDS)-set(cfg)
            extra=set(cfg)-set(DEFAULT_CLAN_FIELDS)
            raise ValueError(f'{nom}: paramètres manquants {missing}, inconnus {extra}.')
        for key,default in DEFAULT_CLAN_FIELDS.items():
            v=cfg[key]
            if isinstance(default,bool) and type(v)!=bool:
                raise ValueError(f'{nom}.{key} doit être true ou false.')
            if type(default)==int and (type(v)!=int or not 0<=v<=12):
                raise ValueError(f'{nom}.{key} doit être un entier entre 0 et 12.')
            if isinstance(default,str) and v not in ['water','wood','flint','bone','plant']:
                raise ValueError(f'{nom}.{key} doit être une ressource connue.')
        if cfg['deplacement']<1 or cfg['chasse_grande_accompagnateurs']<1 or not 1<=cfg['niveau_chamane_depart']<=3:
            raise ValueError(f'{nom}: déplacement, compagnons et niveau de chamane invalides.')
    return True

def sauvegarder_configuration(chemin,data):
    """Enregistre les réglages avec caractères accentués lisibles."""
    valider_configuration(data)
    Path(chemin).write_text(json.dumps(data,ensure_ascii=False,indent=2),encoding='utf-8')

# ========= MOTEUR DE SIMULATION =========
# Chaque terrain possède les six emplacements indiqués à la page 7 de la règle.
TERRAIN_SLOTS = {
    'plaine':['plant','plant','wood','large','flint','water'],
    'colline':['large','large','wood','flint','plant','water'],
    'foret':['wood','wood','wood','medium','plant','small'],
    'riviere':['water','water','water','small','medium','plant'],
    'montagne':['flint','flint','wood','medium','plant','water'],
    'desert':['flint','flint','bone','bone','wood','small'],
}
POOL = {'plaine':8, 'colline':7, 'foret':8, 'riviere':5, 'montagne':5, 'desert':4}
PAIR = {'plaine':['cerf','serpent'], 'colline':['ours','aigle'], 'foret':['loup','sanglier'], 'riviere':['saumon','castor']}
PREF = {c:t for t,clans in PAIR.items() for c in clans}
PREF_SLOT = {'plaine':'flint', 'colline':'flint','foret':'wood','riviere':'water'}
SPEED = {'cerf':3,'serpent':1,'ours':2,'aigle':2,'loup':3,'sanglier':2,'saumon':2,'castor':1}
POLICIES = ['toujours','jamais','aleatoire','favorable']
STRATEGIES = ['survie','chasse','construction','exploration','echanges']
RES = ['food','water','wood','flint','bone','skin','med','magic']
COORDS = [(q,r) for q in range(-3,4) for r in range(-3,4) if max(abs(q),abs(r),abs(q+r))<=3]
CENTRAL=set(COORDS)
DIRS=[(1,0),(0,1),(-1,1),(-1,0),(0,-1),(1,-1)]
def neighbors(pos):
    q,r=pos
    return [(q+dq,r+dr) for dq,dr in DIRS]
def hdist(a,b):
    dq,dr=a[0]-b[0],a[1]-b[1]
    return max(abs(dq),abs(dr),abs(dq+dr))
def xy(pos):
    q,r=pos
    return (math.sqrt(3)*(q+r/2),1.5*r)

# Quatre emplacements extérieurs au grand hexagone, chacun adjacent à deux tuiles.
def seat_cells():
    outer={p for c in COORDS for p in neighbors(c) if p not in CENTRAL}
    edges=[p for p in outer if sum(1 for x in neighbors(p) if x in CENTRAL)==2]
    chosen=[]
    for vx,vy in [(0,-1),(1,0),(0,1),(-1,0)]:
        avail=[p for p in edges if all(hdist(p,z)>=3 for z in chosen)]
        chosen.append(max(avail,key=lambda p:(xy(p)[0]*vx+xy(p)[1]*vy)/max(0.1,math.hypot(*xy(p)))))
    return chosen
SEATS=seat_cells()

# Les compétences sont portées par les personnages (1 à 3 anneaux).
ROLES=[('chasse','cueil'),('chasse','cueil'),('explore','chasse'),('explore','cueil'),('chaman','cueil'),('artisan','chasse')]
@dataclass
class Member:
    skills:dict
    pos:tuple
    slot:int=-1
    used:bool=False
    sick:int=0

@dataclass
class Player:
    seat:int
    clan:str
    policy:str
    strategy:str
    start:tuple
    stock:dict
    members:list
    score_extra:int=0
    exploration_points:int=0  # Points immédiats d'exploration : séparés des trocs.
    food_origins:dict=field(default_factory=lambda: {'animale':0,'vegetale':0,'non_classee':0})
    events:int=0
    offers:int=0
    accepted:int=0
    rejected:int=0
    proposed_success:int=0
    huts:int=0
    built_this_season:bool=False
    desert_paid_this_season:bool=False
    passages_payes:int=0
    cave:tuple|None=None
    shelter_misses:int=0
    unmet:int=0
    penalties:int=0
    hunts_small:int=0
    hunts_medium:int=0
    hunts_large:int=0
    mammoths:int=0
    discoveries:int=0
    injuries:int=0
    no_build:bool=False
    extra_move:int=0
    dice_bonus:int=0
    reroll:int=0
    pending:list=field(default_factory=list)
    armory:dict=field(default_factory=lambda:{1:0,2:0,3:0})
    rule:dict=field(default_factory=dict)
    trade_points:int=0
    trade_bonus_this_season:int=0

# Utilités relatives pour comparer des propositions de troc ; ce n'est pas une règle du jeu.
def val(p,resource,count=1,season=0):
    have=p.stock.get(resource,0)
    base={'food':2.3,'water':2.4,'wood':1.45,'flint':1.05,'bone':1.0,'skin':1.7,'med':1.0,'magic':.8}[resource]
    if resource=='food': target=4 if season>=4 else 3
    elif resource=='water':target=2
    elif resource=='wood':target=3 if season%4 in (2,3) else 2
    elif resource=='skin':target=1 if season%4 in (2,3) else 1
    elif resource in ('bone','flint'):target=2
    else:target=1
    if p.strategy=='survie' and resource in ('food','water'):base*=1.22
    if p.strategy=='chasse' and resource in ('flint','bone','wood'):base*=1.22
    if p.strategy=='construction' and resource in ('skin','wood','bone'):base*=1.45
    if p.strategy=='echanges' and resource in ('wood','bone','flint'):base*=0.95
    if resource=='food' and p.clan in ('serpent','loup','ours','sanglier'):base*=1.15
    if resource=='water' and p.clan=='saumon':base*=1.38
    return sum(base*(1.8 if have+i<target else (0.8 if have+i<target+3 else .38)) for i in range(count))

def add(p,r,n=1,source=None):
    """Ajoute une ressource et, s'il s'agit d'aliments, suit leur origine.

    'source' doit être animale, vegetale ou non_classee. Une carte ou un
    bonus sans origine explicite est honnêtement classé 'non_classee'.
    """
    if n < 0: raise ValueError('Une quantité ajoutée ne peut pas être négative.')
    p.stock[r]=p.stock.get(r,0)+n
    if r=='food':
        provenance=source if source in ('animale','vegetale') else 'non_classee'
        p.food_origins[provenance]+=n

def retirer_nourriture(p,n=1):
    """Consomme les aliments et restitue leur provenance pour un éventuel troc.

    Hypothèse : utiliser d'abord la nourriture non classée, ensuite végétale,
    enfin animale. Il ne s'agit pas d'une obligation prévue dans la règle.
    """
    rest=min(n,p.stock.get('food',0))
    retirees={'animale':0,'vegetale':0,'non_classee':0}
    for origine in ('non_classee','vegetale','animale'):
        q=min(rest,p.food_origins[origine])
        p.food_origins[origine]-=q
        retirees[origine]+=q
        rest-=q
    obtenu=sum(retirees.values())
    p.stock['food']-=obtenu
    return retirees

def take(p,r,n=1):
    """Retire au maximum n ressources, sans descendre sous zéro."""
    if r=='food':
        return sum(retirer_nourriture(p,n).values())
    k=min(n,p.stock.get(r,0))
    p.stock[r]-=k
    return k

def transfert_ressource(donneur,receveur,r):
    """Effectue un vrai transfert d'une ressource, provenance alimentaire comprise."""
    if r=='food':
        for origine,q in retirer_nourriture(donneur).items():
            if q:add(receveur,'food',q,source=origine)
    elif take(donneur,r):
        add(receveur,r)

def food_take(p,n):
    return take(p,'food',n)

def pscore(p):
    return (p.score_extra+sum(p.stock.get(r,0)*({'med':2,'magic':3,'skin':3}.get(r,1)) for r in RES)
            +sum(sum((2 if k=='chaman' else 1)*v for k,v in m.skills.items()) for m in p.members)
            +7*p.huts+(10 if p.cave is not None else 0))

# Les neuf catégories suivantes reconstruisent le score final, sans double compte.
# La catégorie « nourriture sans origine » est nécessaire pour les ressources
# initiales et certains effets de cartes ou avantages de clan non explicités.
CHAMPS_POINTS = [
 ('points_grottes','Grottes','#69739b'),
 ('points_huttes','Huttes','#c5844c'),
 ('points_trocs','Trocs','#67a17c'),
 ('points_explorations','Explorations','#84a8c8'),
 ('points_nourriture_animale','Nourr. animale','#c65e52'),
 ('points_nourriture_vegetale','Nourr. végétale','#7db263'),
 ('points_nourriture_non_classee','Nourr. n/c','#9fa1a2'),
 ('points_autres_ressources','Autres ressources','#c1a05b'),
 ('points_anneaux','Anneaux','#8f74b0'),
 ('points_autres_bonus','Autres bonus','#a58c8a'),
]

def decomposer_points(p):
    """Décompose uniquement les points qui existent à la fin de la partie."""
    anneaux=sum(sum((2 if k=='chaman' else 1)*v for k,v in m.skills.items()) for m in p.members)
    valeur={'med':2,'magic':3,'skin':3}
    autres=sum(p.stock[r]*valeur.get(r,1) for r in RES if r!='food')
    restant_bonus=p.score_extra-p.trade_points-p.exploration_points
    detail={
        'points_grottes':10 if p.cave is not None else 0,
        'points_huttes':7*p.huts,
        'points_trocs':p.trade_points,
        'points_explorations':p.exploration_points,
        'points_nourriture_animale':p.food_origins['animale'],
        'points_nourriture_vegetale':p.food_origins['vegetale'],
        'points_nourriture_non_classee':p.food_origins['non_classee'],
        'points_autres_ressources':autres,
        'points_anneaux':anneaux,
        'points_autres_bonus':restant_bonus,
    }
    # Deux rapprochements utiles : origine des aliments et score complet.
    assert sum(p.food_origins.values())==p.stock['food'], 'Incohérence des nourritures.'
    assert sum(detail.values())==pscore(p), 'Le détail ne correspond pas au score final.'
    return detail

def skill(p,which):
    return max([m.skills.get(which,0) for m in p.members] or [0])

def dice(rng):
    return rng.randint(1,6)+rng.randint(1,6)

def injure(p,rng,until_next=False):
    if p.rule.get('immunite_blessure'):return
    choices=[m for m in p.members if m.sick==0]
    if choices:
        rng.choice(choices).sick=2 if until_next else 1
        p.injuries+=1

# Les blessures concernent la saison en cours ou la prochaine, selon l'événement.
# Pas de modèle de mortalité : la nouvelle règle ne prévoit pas de décès par défaut.
def event_effect(g,p,cid,rng,season):
    # Seuls des effets directement transposables des cartes disponibles sont codés.
    # Les cartes conservables sont jouées dans leur forme simplifiée (immédiate).
    rec=[p] if cid not in g.public_events else g.players
    for x in rec:
        if cid in g.detrimental and x.clan in ('aigle','sanglier') and x is not p:
            pass
        if cid in (1,):add(x,'water')
        elif cid==2:add(x,'food',source='vegetale');add(x,'med')
        elif cid==3:add(x,'water',2)
        elif cid==4:x.extra_move+=1
        elif cid==5:add(x,'food',source='vegetale')  # timing adapté : récolte saisonnière simplifiée
        elif cid==6:add(x,'food',source='vegetale')
        elif cid==7:loss(x,'water',1,'water')
        elif cid==8:loss(x,'food',1,'food')
        elif cid==9:loss(x,'wood',1);loss(x,'water',1,'water')
        elif cid==10:
            if take(x,'skin')==0:injure(x,rng)
        elif cid==11:loss(x,'food',1,'food')
        elif cid==12:loss(x,'wood',2)
        elif cid==13:
            if skill(x,'chasse')>=2:add(x,'food',source='animale')
        elif cid==14:
            if any(g.tiles.get(m.pos)=='riviere' for m in x.members):add(x,'food',source='animale')
        elif cid==15:add(x,'bone')
        elif cid==16:
            if skill(x,'chasse')>=2:add(x,'skin');add(x,'bone')
        elif cid==17:
            if sum(m.skills.get('chasse',0)>=3 for m in x.members)>=2:add(x,'food',2,source='animale');add(x,'skin');add(x,'bone')
        elif cid==18:loss(x,'food',2,'food')
        elif cid==19 and x.clan!='sanglier':injure(x,rng)
        elif cid==20 and x.clan!='ours':loss(x,'food',2,'attack')
        elif cid==21:loss(x,'food',1,'food')
        elif cid==22:
            if skill(x,'chaman')==0:injure(x,rng)
        elif cid==23:add(x,'food',2,source='vegetale')
        elif cid==24:add(x,'med')
        elif cid==25:add(x,'flint',2)
        elif cid==26:add(x,'wood',2)
        elif cid==27:loss(x,'food',1,'food')
        elif cid==28:loss(x,'wood')
        elif cid==29:loss(x,'flint')
        elif cid==30:loss(x,'food',1,'food')
        elif cid in (31,311,312):
            if not x.rule['sans_nomades'] and x.stock['food']>=6 and len(x.members)<9:
                take(x,'food',2)
                role={31:('chasse','cueil'),311:('artisan','chasse'),312:('explore','cueil')}[cid]
                x.members.append(Member({role[0]:1,role[1]:1},x.members[0].pos,used=True))
        elif cid==32:
            if x.stock['food']>=2:take(x,'food');add(x,'flint');add(x,'bone')
        elif cid==33:
            if x.stock['water']>=2:take(x,'water');add(x,'food',2,source='animale');add(x,'skin')
        elif cid==34:
            if x.stock['food']>=2 and any(m.sick for m in x.members):
                take(x,'food');next(m for m in x.members if m.sick).sick=0
        elif cid==35:
            r=max(RES,key=lambda z:x.stock[z])
            if x.stock[r]>0:loss(x,r)
        elif cid==36:loss(x,'food',2,'food')
        elif cid==38:loss(x,'flint');loss(x,'water',1,'water')
        elif cid==39:
            for m in x.members:
                if m.sick:m.sick=0;break
        elif cid==40:
            if len(x.members)<9:x.members.append(Member({'chasse':1,'cueil':1},x.members[0].pos,used=True))
        elif cid==42:
            z=[m for m in x.members if 'explore' in m.skills]
            if z and x.clan!='serpent':rng.choice(z).sick=1;x.injuries+=1
        elif cid==43:
            if take(x,'med')==0:injure(x,rng)
        elif cid==44:
            loss(x,'flint');z=[m for m in x.members if 'artisan' in m.skills]
            if z and x.clan!='serpent':z[0].sick=1;x.injuries+=1
        elif cid==45:
            for m in x.members:
                if 'chaman' in m.skills:m.skills['chaman']=min(3,m.skills['chaman']+1);break
        elif cid==46:
            for m in x.members:
                if 'chaman' in m.skills:m.skills['chaman']=min(3,m.skills['chaman']+1);break
        elif cid==47:add(x,'flint');add(x,'bone')
        elif cid==48:
            for m in x.members:
                if 'chaman' in m.skills and m.skills['chaman']>1:m.skills['chaman']-=1;break
            else:loss(x,'food')
        elif cid==49:
            if take(x,'wood')==0:loss(x,'food',1,'food')
        elif cid==50:loss(x,'wood');loss(x,'skin')
        elif cid==51:x.dice_bonus-=1
        elif cid==52:x.dice_bonus+=1
        elif cid==53:loss(x,'wood') if x.stock['wood']>0 else loss(x,'water')
        elif cid==54:x.no_build=True
        elif cid==55:x.extra_move-=1
        elif cid==56:x.dice_bonus+=3
        elif cid==57:x.extra_move+=1
        elif cid==58:pass # anticipation de futures cartes non fidèlement simulable
        elif cid==59:add(x,'food',source='animale')
        elif cid==60:loss(x,'food',2,'attack')
        elif cid==61:loss(x,'skin')
        elif cid==62:loss(x,'food',1,'food')
        elif cid==63:
            if x.huts and not x.rule['hutte_immunisee']:loss(x,'food',1,'food')
        elif cid==64:x.dice_bonus+=3
        elif cid==65:x.reroll+=1

def loss(p,r,n=1,kind=''):
    if kind=='attack' and p.rule['immunite_evenements_attaque']:add(p,'food');return
    if kind=='food' and p.rule['immunite_evenements_nourriture']:return
    if kind=='water' and p.rule['immunite_evenements_eau']:return
    take(p,r,n)

class Game:
    public_events={1,5,7,8,11,14,21,24,29,46,54}
    detrimental={7,8,9,10,11,12,18,19,20,21,22,27,28,29,30,35,36,38,42,43,44,48,49,50,51,53,54,55,60,61,62,63}
    def __init__(self,rng,season_count,events=True,config=None):
        self.config=config or configuration_defaut()
        self.rng=rng;self.season_count=season_count;self.with_events=events
        # Le même nombre et la même nature de tuiles figurent dans chaque partie.
        bag=[t for t,n in POOL.items() for _ in range(n)];rng.shuffle(bag)
        self.tiles=dict(zip(COORDS,bag))
        self.revealed=set()
        self.occupied={}
        self.deck=[i for i in range(1,66) if i not in (37,41)]+[311,312]
        rng.shuffle(self.deck)
        self.players=[]
        types=list(PAIR);rng.shuffle(types)
        policies=POLICIES[:];rng.shuffle(policies)
        strategies=STRATEGIES[:];rng.shuffle(strategies)
        # Cinquième stratégie : quatre places seulement ; sélection équilibrée en moyenne.
        chosen_strategies=rng.sample(STRATEGIES,4)
        for seat in range(4):
            terrain=types[seat];clan=rng.choice(PAIR[terrain]);spot=SEATS[seat]
            self.tiles[spot]=terrain;self.revealed.add(spot)
            members=[Member({role[0]:1,role[1]:1},spot) for role in ROLES]
            rules=self.config['clans'][clan]
            members[4].skills['chaman']=rules['niveau_chamane_depart']
            stock={r:0 for r in RES}
            stock.update({'food':4 if season_count==4 else 3,'water':2 if season_count==4 else 1,
                          'wood':2 if season_count==4 else 1,'flint':1,'bone':1})
            if season_count==4:
                members[0].skills['chasse']=2
                members[1].skills['cueil']=2
            # La règle ne précise pas l'origine des nourritures données au départ.
            aliments_depart=stock['food']
            self.players.append(Player(seat,clan,policies[seat],chosen_strategies[seat],spot,stock,members,
                rule=rules,food_origins={'animale':0,'vegetale':0,'non_classee':aliments_depart}))
        self.tradelog=[]
        self.trace=[]
    def drawn(self,p,season):
        if not self.with_events:return
        def one():
            if not self.deck:
                self.deck=[i for i in range(1,66) if i not in (37,41)]+[311,312];self.rng.shuffle(self.deck)
            return self.deck.pop()
        cards=[one() for _ in range(2 if p.rule['choix_deux_evenements'] else 1)]
        if len(cards)==2:
            # Fiches : le joueur choisit la meilleure carte après inspection.
            card=max(cards,key=lambda c:(1 if c not in self.detrimental else -1)*2+self.rng.random()*.2)
        else:card=cards[0]
        # Choix du chaman : une carte réellement défavorable peut être annulée.
        sh=next((m for m in p.members if 'chaman' in m.skills),None)
        if card in self.detrimental and sh and sh.skills['chaman']>=2 and self.rng.random()<.35:
            sh.skills['chaman']-=1
            return
        event_effect(self,p,card,self.rng,season)
        p.events+=1
    def reveal(self,p,season):
        # Explorateur : priorité à une tuile cachée atteignable ; toute carte est retournée avant la récolte.
        explorers=[m for m in p.members if m.skills.get('explore',0)]
        rng=self.rng
        if not explorers:return None
        scout=max(explorers,key=lambda m:m.skills['explore']+rng.random()*.04)
        base=max(1,p.rule['deplacement']+p.extra_move-(p.rule['vitesse_malus_hiver'] if season%4==3 else 0))
        hidden=[t for t in CENTRAL-self.revealed if any(a in self.revealed for a in neighbors(t))]
        allowed=[t for t in hidden if hdist(scout.pos,t)<=base+scout.skills['explore']]
        if not allowed:return None
        # Un débutant découvre le plus souvent les espaces accessibles aux autres membres.
        weighted=sorted(allowed,key=lambda t:(min(hdist(t,m.pos) for m in p.members),rng.random()))
        # En stratégie d'exploration, l'explorateur cherche plus souvent à dépasser
        # la portée normale du clan et peut ainsi progresser dans sa spécialité.
        far=[z for z in allowed if base < hdist(scout.pos,z) <= base+scout.skills['explore']]
        oldpos=scout.pos
        if far and (p.strategy=='exploration' or rng.random()<.22):
            t=min(far,key=lambda z:hdist(z,p.start))
        else:
            t=weighted[0] if rng.random()<.72 else rng.choice(allowed)
        # Aigle : choix secret entre deux tuiles connues du simulateur.
        if p.rule['consultation_deux_tuiles'] and len(allowed)>1:
            other=rng.choice([z for z in allowed if z!=t])
            def terrain_value(z):
                slots=TERRAIN_SLOTS[self.tiles[z]]
                return sum(1.5 if x in ('plant','water') else 1 for x in slots)+3*(self.tiles[z]==PREF[p.clan])
            if terrain_value(other)>terrain_value(t):t=other
        self.revealed.add(t);p.discoveries+=1
        scout.used=True;scout.pos=t
        if hdist(t,p.start)>0:
            points=2 if self.tiles[t]==PREF[p.clan] else 1
            p.score_extra+=points
            p.exploration_points+=points
        if hdist(t,oldpos)>base and scout.skills['explore']<3:scout.skills['explore']+=1
        # L'explorateur qui arrive sur cette tuile y reste cette saison.
        scouts=[scout]
        # Une stratégie exploratrice emploie parfois le deuxième explorateur
        # pour retourner une tuile supplémentaire, sans dépasser trois au total.
        if p.strategy=='exploration':
            others=[m for m in explorers if m is not scout and not m.used and not m.sick]
            if others:
                second=others[0]
                remaining=[z for z in CENTRAL-self.revealed
                           if any(a in self.revealed for a in neighbors(z))
                           and hdist(second.pos,z)<=base+second.skills['explore']]
                if remaining:
                    z=min(remaining,key=lambda pos:(hdist(pos,second.pos),rng.random()))
                    self.revealed.add(z);p.discoveries+=1
                    points=2 if self.tiles[z]==PREF[p.clan] else 1
                    p.score_extra+=points
                    p.exploration_points+=points
                    if hdist(second.pos,z)>base and second.skills['explore']<3:
                        second.skills['explore']+=1
                    second.used=True;second.pos=z;scouts.append(second)
        return scouts
    def location_choices(self,p,m,free):
        speed=max(1,p.rule['deplacement']+p.extra_move-(p.rule['vitesse_malus_hiver'] if getattr(self,'current_season',0)%4==3 else 0))
        if 'explore' in m.skills:speed+=m.skills['explore']
        return [t for t in self.revealed if hdist(m.pos,t)<=speed and
                (not p.rule['interdit_desert'] or self.tiles[t]!='desert') and
                sum(1 for (z,s) in self.occupied if z==t)<3] or [m.pos]
    def choose_slots(self,p,group,season,goal=None):
        # Les groupes contraints voyagent à deux (ou à trois avec la naissance).
        common=set(self.location_choices(p,group[0],self.occupied))
        for m in group[1:]:common&=set(self.location_choices(p,m,self.occupied))
        if not common:common={group[0].pos}
        ranked=[]
        for t in common:
            if sum(1 for (pos,slot) in self.occupied if pos==t)+len(group)>3 and t not in SEATS:continue
            slots=[i for i in range(6) if (t,i) not in self.occupied]
            if len(slots)<len(group):continue
            score,choices=self.assign_slots(p,group,t,slots,season)
            if p.strategy=='exploration':score+=.20*hdist(t,p.start)
            if p.strategy=='echanges':
                # La stratégie d'échange se rapproche physiquement des autres clans.
                others=[z.pos for other in self.players if other is not p for z in other.members]
                if others:score+=max(0,4-min(hdist(t,pos) for pos in others))*.6
            score+=self.rng.uniform(-.27,.27)
            ranked.append((score,t,choices))
        if not ranked:return []
        best=max(ranked,key=lambda a:a[0]);return [(m,best[1],i) for m,i in zip(group,best[2])]
    def slot_score(self,p,m,t,slot,season):
        typ=TERRAIN_SLOTS[self.tiles[t]][slot]
        if m.sick:return -.4
        if 'explore' in m.skills and m.used:return -.2
        if typ=='plant' and 'cueil' in m.skills:
            if p.stock['food']<5:return val(p,'food',season=season)
            if m.skills['cueil']==1:return val(p,'food',season=season)+.8
            if m.skills['cueil']==2:return max(val(p,'food',season=season),val(p,'med',season=season))+.7
            return max(val(p,'food',season=season),val(p,'magic',season=season))+.2
        if typ in ('water','wood','flint','bone'):
            key=typ
            v=val(p,key,season=season)
            if typ==p.rule['bonus_ressource'] and self.tiles[t]==PREF[p.clan]:v*=1+p.rule['bonus_quantite']*.9
            return v
        if typ in ('small','medium','large') and 'chasse' in m.skills:
            lvl=m.skills['chasse']
            need={'small':1,'medium':2,'large':3}[typ]
            if lvl<need:return -.7
            if typ=='large' and not any(z is not m and 'chasse' in z.skills and z.pos==t for z in p.members):
                return 2.0 if p.strategy=='chasse' else .4
            return {'small':3.5,'medium':6.2,'large':9.3}[typ]*(1.25 if p.strategy=='chasse' else 1)
        return -.8
    def assign_slots(self,p,members,t,slots,season):
        # Recherche exhaustive sur 6 emplacements maximum et 3 personnages.
        from itertools import permutations
        # La valeur d'une case ne dépend pas des autres cases choisies.
        # Pré-calcul indispensable : évite 120 fois les mêmes évaluations.
        matrix=[[self.slot_score(p,m,t,i,season) for i in slots] for m in members]
        by_slot={z:k for k,z in enumerate(slots)}
        best_score=-1e10;best=[]
        for assignment in permutations(slots,len(members)):
            score=sum(matrix[j][by_slot[slot]] for j,slot in enumerate(assignment))
            if score>best_score:best_score=score;best=assignment
        return best_score,best
    def place(self,p,season,scouts):
        rng=self.rng
        members=p.members
        for m in members:m.slot=-1
        # L'explorateur découvreur a déjà dépensé son action en exploration.
        for scout in (scouts or []):
            slots=[i for i in range(6) if (scout.pos,i) not in self.occupied]
            if slots:
                z=rng.choice(slots);scout.slot=z;self.occupied[(scout.pos,z)]=p
        left=[m for m in members if m not in (scouts or [])]
        # Pour les clans non dispersés, les non-explorateurs restent par deux ou trois.
        if p.rule['dispersion_libre']:
            groups=[[m] for m in left]
        else:
            ex=[[m] for m in left if 'explore' in m.skills]
            commons=[m for m in left if 'explore' not in m.skills]
            groups=ex+[commons[i:i+2] for i in range(0,len(commons),2)]
            if len(commons)%2 and len(groups)>=2:
                # Le membre surnuméraire rejoint la dernière paire.
                stray=groups.pop()
                if len(stray)==1:
                    dest=next((g for g in groups if len(g)==2),None)
                    if dest:dest.extend(stray)
                    else:groups.append(stray)
                else:groups.append(stray)
        rng.shuffle(groups)
        for group in groups:
            placements=self.choose_slots(p,group,season)
            for m,t,i in placements:
                if (t,i) not in self.occupied:
                    m.pos=t;m.slot=i;self.occupied[(t,i)]=p
            # Si les ressources n'ont pas pu être allouées, le personnage reste au centre.
        visited={m.pos for m in members if m.slot>=0}
        if not p.desert_paid_this_season and any(self.tiles[t]=='desert' for t in visited):
            if p.rule['eau_cout_desert']:
                take(p,'water',p.rule['eau_cout_desert'])
            p.desert_paid_this_season=True
        # Péage simplifié de sous-nombre : une ressource sur chaque tuile concernée.
        for t in visited:
            own=sum(m.pos==t and m.slot>=0 for m in members)
            other_members=[(other,sum(m.pos==t and m.slot>=0 for m in other.members))
                           for other in self.players if other is not p]
            other,count=max(other_members,key=lambda item:item[1])
            if count>own and any(p.stock[r]>0 for r in RES):
                res=max(RES,key=lambda r:p.stock[r])
                if p.stock[res]>0:
                    transfert_ressource(p,other,res);p.passages_payes+=1
    def gather_and_hunt(self,p,season):
        rng=self.rng
        # Priorité à l'artisan : une action unique, mais fabrication multiple autorisée.
        artisan=next((m for m in p.members if 'artisan' in m.skills),None)
        active=[m for m in p.members if m.slot>=0 and not m.used and not m.sick]
        hunters=[m for m in active if 'chasse' in m.skills and TERRAIN_SLOTS[self.tiles[m.pos]][m.slot] in ('small','medium','large')]
        if artisan and not artisan.sick:
            # Une arme peut être fabriquée, conservée, puis utilisée plus tard.
            armable=[]
            for hunter in hunters:
                typ=TERRAIN_SLOTS[self.tiles[hunter.pos]][hunter.slot]
                lvl={'small':1,'medium':2,'large':3}[typ]
                if hunter.skills['chasse']>=lvl:armable.append((hunter,lvl))
            armable.sort(key=lambda z:z[1],reverse=p.strategy=='chasse')
            for hunter,lvl in armable:
                if lvl>artisan.skills['artisan']+1:continue
                if lvl==3 and p.stock['food']<1:continue
                if p.armory[lvl]>=1:
                    p.armory[lvl]-=1
                    hunter._armed=lvl
                    continue
                mats=sorted(['wood','flint','bone'],key=lambda z:(p.stock[z]==0,p.stock[z]))
                chosen=[key for key in mats if p.stock[key]>=1][:lvl]
                if len(chosen)<lvl:continue
                for key in chosen:take(p,key)
                hunter._armed=lvl
                artisan.used=True
                if lvl==2 and artisan.skills['artisan']==1:artisan.skills['artisan']=2
                if lvl==3 and artisan.skills['artisan']==2:artisan.skills['artisan']=3
            # En l'absence de chasse, le joueur peut fabriquer une arme et la stocker.
            # Cela permet notamment à l'artisan d'évoluer vers la fabrication d'abris.
            if not artisan.used and (p.strategy in ('construction','survie') or self.rng.random()<.40):
                lvl=2 if artisan.skills['artisan']==1 else 3 if artisan.skills['artisan']==2 else 0
                if lvl and p.armory[lvl]<1:
                    mats=sorted(['wood','flint','bone'],key=lambda z:(p.stock[z]==0,p.stock[z]))
                    chosen=[key for key in mats if p.stock[key]>=1][:lvl]
                    if len(chosen)==lvl:
                        for key in chosen:take(p,key)
                        p.armory[lvl]+=1
                        artisan.skills['artisan']+=1
                        artisan.used=True
        for m in list(active):
            if m.used:continue
            typ=TERRAIN_SLOTS[self.tiles[m.pos]][m.slot]
            if typ in ('water','wood','flint','bone'):
                gain=(1+p.rule['bonus_quantite']) if typ==p.rule['bonus_ressource'] and self.tiles[m.pos]==PREF[p.clan] else 1
                add(p,typ,gain)
                if typ=='wood' and season%4 in (2,3):add(p,'wood',p.rule['bois_bonus_automne_hiver'])
                if self.tiles[m.pos]=='riviere':add(p,'food',p.rule['nourriture_bonus_riviere'])
                if 'water' in TERRAIN_SLOTS[self.tiles[m.pos]]:add(p,'food',p.rule['nourriture_bonus_tuile_eau'])
                m.used=True
            elif typ=='plant' and 'cueil' in m.skills:
                lvl=m.skills['cueil']
                if lvl==1 or p.stock['food']<=3:target='food'
                elif lvl==2:target='med' if p.stock['med']<2 and p.stock['food']>=6 else 'food'
                else:target='magic' if p.stock['food']>=7 else 'food'
                add(p,target,1+(p.rule['plante_bonus_plaine_foret'] if self.tiles[m.pos] in ('foret','plaine') else 0),
                    source='vegetale' if target=='food' else None)
                if target=='food' and self.tiles[m.pos]=='foret' and season%4 in (0,1):add(p,'food',p.rule['nourriture_foret_printemps_ete'],source='vegetale')
                if self.tiles[m.pos]=='riviere':add(p,'food',p.rule['nourriture_bonus_riviere'])
                if 'water' in TERRAIN_SLOTS[self.tiles[m.pos]]:add(p,'food',p.rule['nourriture_bonus_tuile_eau'])
                if target=='food' and lvl==1:m.skills['cueil']=2
                if target=='med' and lvl==2:m.skills['cueil']=3
                m.used=True
            elif typ in ('small','medium','large') and 'chasse' in m.skills:
                lvl={'small':1,'medium':2,'large':3}[typ]
                if m.skills['chasse']<lvl or getattr(m,'_armed',0)<lvl:continue
                if lvl==3:
                    companions=[z for z in p.members if z is not m and z.pos==m.pos and 'chasse' in z.skills and z.slot>=0 and z.sick==0]
                    if len(companions)<p.rule['chasse_grande_accompagnateurs'] or p.stock['food']<1:continue
                    food_take(p,1)
                    roll=dice(rng)+p.dice_bonus
                    if roll<7 and p.reroll: p.reroll-=1;roll=dice(rng)
                    if roll<7:
                        sh=next((z for z in p.members if z.skills.get('chaman',0)>=2),None)
                        if sh and p.stock['food']>=2 and rng.random()<.5:
                            food_take(p,1);sh.skills['chaman']-=1;roll=dice(rng)
                    p.hunts_large+=1
                    n=2 if roll>=11 else 1 if roll>=7 else 0
                    if n:
                        add(p,'food',6*n,source='animale');add(p,'skin',2*n);add(p,'bone',2*n);p.mammoths+=n
                    elif roll<=3:injure(p,rng,until_next=True)
                    for z in companions[:p.rule['chasse_grande_accompagnateurs']]:z.used=True
                elif lvl==2:
                    roll=dice(rng)+p.dice_bonus
                    if roll<7 and p.reroll:p.reroll-=1;roll=dice(rng)
                    if roll<7:
                        sh=next((z for z in p.members if z.skills.get('chaman',0)>=2),None)
                        if sh and p.stock['food']>=2 and rng.random()<.5:
                            food_take(p,1);sh.skills['chaman']-=1;roll=dice(rng)
                    p.hunts_medium+=1
                    if roll>=7:
                        add(p,'food',2,source='animale');add(p,'skin');add(p,'bone')
                        if m.skills['chasse']==2:m.skills['chasse']=3
                else:
                    p.hunts_small+=1;add(p,'food',source='animale')
                    if m.skills['chasse']==1:m.skills['chasse']=2
                if ((lvl==1) or (lvl==2 and roll>=7) or (lvl==3 and n)):
                    add(p,'bone',p.rule['os_bonus_chasse'])
                    if sum(z.pos==m.pos for z in p.members)>=3:add(p,'food',p.rule['nourriture_bonus_chasse_groupe'],source='animale')
                if 'water' in TERRAIN_SLOTS[self.tiles[m.pos]]:
                    add(p,'food',p.rule['nourriture_bonus_tuile_eau'])
                if self.tiles[m.pos]=='riviere':add(p,'food',p.rule['nourriture_bonus_riviere'])
                m.used=True
                if hasattr(m,'_armed'):del m._armed
        # Aucune activité supplémentaire après une action personnelle.
    def shelters(self,p,season):
        # Une grotte ne reste propriété du clan que si un membre la garde.
        if p.cave is not None and not any(m.pos==p.cave for m in p.members):
            p.cave=None
        # Le bâtisseur peut construire un nouvel abri de valeur, même avec une grotte.
        # Une seule construction par tour dans ce modèle expérimental.
        if p.strategy=='construction' and not p.no_build and p.huts<2:
            artisan=next((m for m in p.members if m.skills.get('artisan',0)>=3 and not m.sick),None)
            materials=['wood','bone']+['wood']*p.rule['surcout_hutte_bois']+['bone']*p.rule['surcout_hutte_os']
            if p.rule['cout_hutte_castor_deux_bois']:materials=['wood','wood']
            count=collections.Counter(materials)
            if artisan and p.stock['skin']>=1 and all(p.stock[r]>=num for r,num in count.items()):
                take(p,'skin')
                for r,num in count.items():take(p,r,num)
                p.huts+=1;p.built_this_season=True;artisan.used=True
        if p.cave is None:
            mount=[m.pos for m in p.members if self.tiles.get(m.pos)=='montagne']
            if mount:
                c=mount[0]
                if c not in [x.cave for x in self.players] and dice(self.rng)>=9:
                    p.cave=c
        if season%4==3 and not p.built_this_season and p.cave is None and p.huts<(season//4+1):
            artisan=next((m for m in p.members if m.skills.get('artisan',0)>=3),None)
            if artisan and not p.no_build and p.stock['skin']>=1:
                cost=['wood','bone']
                cost+=['bone']*p.rule['surcout_hutte_os']+['wood']*p.rule['surcout_hutte_bois']
                if p.rule['cout_hutte_castor_deux_bois']:cost=['wood','wood']
                needed=collections.Counter(cost)
                if all(p.stock[x]>=n for x,n in needed.items()):
                    take(p,'skin')
                    for x,n in needed.items():take(p,x,n)
                    p.huts+=1
    def seasonal_payment(self,p,season):
        typ=season%4
        need={'food':4 if len(p.members)>=7 else 3,'water':[1,2,2,1][typ]}
        need['water']+=p.rule['eau_supplementaire_saison']
        need['food']+=p.rule['nourriture_supplementaire_saison']
        if typ==2:need['food']+=p.rule['nourriture_supplementaire_automne']
        if typ==3:need['food']+=p.rule['nourriture_supplementaire_hiver']
        if typ==2:need.update({'wood':1,'skin':0 if p.rule['pas_de_peau_saison'] else 1})
        if typ==3:need.update({'wood':2,'skin':0 if p.rule['pas_de_peau_saison'] else 1})
        for key,n in need.items():
            delta=n-take(p,key,n)
            if delta>0:
                p.unmet+=delta
                for _ in range(delta):
                    removable=[(m,k) for m in p.members for k,v in m.skills.items() if v>1 and k!='chaman']
                    if removable:
                        z,k=self.rng.choice(removable);z.skills[k]-=1;p.penalties+=1
                    else:
                        injure(p,self.rng,until_next=True)
        if typ==3 and p.cave is None and p.huts<season//4+1:
            p.shelter_misses+=1
            for _ in range(2):
                removable=[(m,k) for m in p.members for k,v in m.skills.items() if v>1 and k!='chaman']
                if removable:
                    z,k=self.rng.choice(removable);z.skills[k]-=1;p.penalties+=1
        if season<self.season_count-1:
            for m in p.members:
                if m.skills.get('chaman',0)>0:m.skills['chaman']=min(3,m.skills['chaman']+1)
    def consider_trades(self,p,season):
        """Échanges de ressource contre ressource, sans troc fictif réciproque.

        Les propositions sont dirigées vers les voisins présents à <=1 tuile.
        Accepter est libre ; seul le BONUS peut être plafonné selon configuration.
        """
        options=self.config['simulation']
        n_offers=options['maximum_offres_par_tour']
        # La stratégie « échanges » bénéficie des mêmes limites par défaut,
        # mais privilégie des propositions gagnant-gagnant plutôt que son seul gain.
        for _ in range(n_offers):
            others=[x for x in self.players if x is not p and any(
                hdist(a.pos,b.pos)<=1 for a in p.members for b in x.members)]
            if not others:break
            candidates=[]
            for other in others:
                for give in RES:
                    if p.stock[give]<1:continue
                    for want in RES:
                        if want==give or other.stock[want]<1:continue
                        gain=val(p,want,season=season)-val(p,give,season=season)
                        receiver_gain=val(other,give,season=season)-val(other,want,season=season)
                        if gain<=.05:continue
                        # L'échange doit être un échange d'objets distincts.
                        benefit=gain+(max(-1,receiver_gain)*.65 if p.strategy=='echanges' else 0)
                        candidates.append((benefit,other,give,want,receiver_gain))
            if not candidates:break
            candidates.sort(key=lambda z:z[0],reverse=True)
            pool=candidates[:min(5,len(candidates))]
            _,other,give,want,delta=self.rng.choice(pool) if self.rng.random()<.25 else pool[0]
            p.offers+=1
            accept=(other.policy=='toujours' or
                    (other.policy=='aleatoire' and self.rng.random()<options['probabilite_troc_aleatoire']) or
                    (other.policy=='favorable' and delta>.05))
            bonus=0
            if accept:
                transfert_ressource(p,other,give);transfert_ressource(other,p,want)
                bonus=min(options['points_par_troc'],max(0,
                    options['maximum_points_troc_par_saison']-other.trade_bonus_this_season))
                other.trade_points+=bonus
                other.trade_bonus_this_season+=bonus
                other.score_extra+=bonus
                other.accepted+=1
                p.proposed_success+=1
            else:
                other.rejected+=1
            self.tradelog.append(dict(saisons=self.season_count,saison=season+1,
                 proposant=p.clan,receveur=other.clan,politique=other.policy,
                 strategie_proposant=p.strategy,strategie_receveur=other.strategy,
                 propose=give,demande=want,utilite_receveur=round(delta,3),
                 accepte=int(accept),bonus_points=bonus))

    def run(self):
        for season in range(self.season_count):
            self.current_season=season
            if season==4:
                for p in self.players:
                    # Le nouveau venu prend un anneau de chasse ET un de cueillette
                    # à des personnages qui en ont au moins deux.
                    newborn=Member({'chasse':1,'cueil':1},p.members[0].pos)
                    for k in ('chasse','cueil'):
                        eligible=[m for m in p.members if m.skills.get(k,0)>1]
                        if eligible:self.rng.choice(eligible).skills[k]-=1
                        # Si aucun anneau transférable : naissance sans transfert (hypothèse de sauvegarde).
                    p.members.append(newborn)
            self.occupied={}
            for p in self.players:
                p.trade_bonus_this_season=0
                p.built_this_season=False
                p.desert_paid_this_season=False
                p.accepted_this_season=False
                p.no_build=False;p.extra_move=0;p.dice_bonus=0;p.reroll=0
                for m in p.members:
                    if m.sick>0:m.sick-=1
                    m.used=False;m.slot=-1
            # Ordre des joueurs tournant, mais les sièges sont fixes pendant une partie.
            order=self.players[season%4:]+self.players[:season%4]
            for p in order:
                scouts=self.reveal(p,season)
                self.drawn(p,season)
                self.place(p,season,scouts)
                self.gather_and_hunt(p,season)
                self.shelters(p,season)
                self.consider_trades(p,season)
            for p in self.players:self.seasonal_payment(p,season)
            if season in (0,3,self.season_count-1):
                self.trace.append({'season':season+1,'mean_score':sum(pscore(p) for p in self.players)/4,
                                   'mean_food':sum(p.stock['food'] for p in self.players)/4,
                                   'mean_unmet':sum(p.unmet for p in self.players)/4})
        scores=[pscore(p) for p in self.players]
        high=max(scores)
        winners=[p for p,s in zip(self.players,scores) if s==high]
        rows=[]
        for p in self.players:
            rows.append({'saisons':self.season_count,'evenements':int(self.with_events),'siege':p.seat,
                         'clan':p.clan,'politique':p.policy,'strategie':p.strategy,'score':pscore(p),
                         'victoire':1/len(winners) if p in winners else 0,
                         'offres':p.offers,'trocs_acceptes':p.accepted,'trocs_refuses':p.rejected,
                         'trocs_propose_reussis':p.proposed_success,'penuries':p.unmet,'anneaux_perdus':p.penalties,
                         'hutte':p.huts,'grotte':int(p.cave is not None),'abris_manquants':p.shelter_misses,
                         'petites_chasses':p.hunts_small,'chasses_moyennes':p.hunts_medium,
                         'grandes_chasses':p.hunts_large,'mammouths':p.mammoths,
                         'explorations':p.discoveries,'blessures':p.injuries,
                         'nourriture_finale':p.stock['food'],'ressources_finales':sum(p.stock.values()),
                         'bonus_troc':p.trade_points,'peages_payes':p.passages_payes,'anneaux_finaux':sum(sum(m.skills.values()) for m in p.members),'membres_finaux':len(p.members),**decomposer_points(p)})
        return rows

def test():
    """Vérifications de base de la topologie et du score."""
    assert len(COORDS)==37 and sum(POOL.values())==37
    assert len(SEATS)==4 and len(set(SEATS))==4
    assert all(sum(z in CENTRAL for z in neighbors(p))==2 for p in SEATS)
    g=Game(random.Random(1),8,True,configuration_defaut())
    rows=g.run()
    assert len(rows)==4 and all(r['score']>=0 for r in rows)
    assert abs(sum(r['victoire'] for r in rows)-1)<1e-8
    # Contrôle le total exact catégorie par catégorie, partie par partie.
    assert all(sum(r[k] for k,_,_ in CHAMPS_POINTS)==r['score'] for r in rows)


# ========= ANALYSE STATISTIQUE ET GRAPHIQUES =========
# Import optionnel : le calcul des statistiques reste possible sans matplotlib.
try:
    import matplotlib
    matplotlib.use('Agg')  # Produit des PNG sans fenêtre graphique.
    import matplotlib.pyplot as plt
    import numpy as np
except ImportError:
    plt=None
    np=None

STRATEGIES=['survie','chasse','construction','exploration','echanges']
POLITIQUES=['toujours','jamais','aleatoire','favorable']
CLANS=['cerf','serpent','ours','aigle','loup','sanglier','saumon','castor']

# Les nombres de simulations ne sont PAS des observations de joueurs humains.
def agreger(lignes):
    """Calcule moyenne, victoires et indicateurs de risque sur un groupe de lignes."""
    n=len(lignes)
    if not n:return {}
    somme=lambda champ:sum(float(z[champ]) for z in lignes)
    scores=[float(z['score']) for z in lignes]
    taux=somme('victoire')/n
    variance=sum((float(z['victoire'])-taux)**2 for z in lignes)/n
    # Demi-largeur asymptotique 95 % : indicative car résultats de parties dépendants.
    marge=1.96*math.sqrt(variance/n)
    return dict(effectif=n,score_moyen=round(statistics.mean(scores),2),
      score_median=round(statistics.median(scores),2),
      taux_victoire=round(100*taux,2),
      marge_95_pts=round(100*marge,2),
      penuries_moyennes=round(somme('penuries')/n,2),
      parties_sans_penurie=round(100*sum(int(z['penuries'])==0 for z in lignes)/n,2),
      anneaux_perdus_moyens=round(somme('anneaux_perdus')/n,2),
      explorations_moyennes=round(somme('explorations')/n,2),
      grandes_chasses_moyennes=round(somme('grandes_chasses')/n,2),
      huttes_moyennes=round(somme('hutte')/n,2),
      grottes_pct=round(100*sum(int(z['grotte'])>0 for z in lignes)/n,2),
      trocs_acceptes_moyens=round(somme('trocs_acceptes')/n,2),
      bonus_troc_moyen=round(somme('bonus_troc')/n,2))

def partition(lignes,cles):
    """Rassemble les résultats selon une ou plusieurs colonnes explicites."""
    groups=defaultdict(list)
    for ligne in lignes:groups[tuple(ligne[c] for c in cles)].append(ligne)
    return groups

def fichier_csv(path,rows):
    """Enregistre les tableaux avec un BOM UTF-8 compatible Excel sur Windows."""
    if not rows:
        Path(path).write_text('Aucune donnée suffisante pour ce tableau.\n',encoding='utf-8-sig')
        return
    with Path(path).open('w',encoding='utf-8-sig',newline='') as file:
        writer=csv.DictWriter(file,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

def analyser_decomposition(lignes,root):
    """Constitue des moyennes par clan et par stratégie, sans inventer de chiffres.

    Les anciens CSV ne stockaient pas la provenance des nourritures : dans ce
    cas, aucun tableau de ventilation n'est généré à partir de suppositions.
    """
    noms=[c for c,_,_ in CHAMPS_POINTS]
    if not lignes or not all(c in lignes[0] for c in noms):
        return {}
    for row in lignes:
        calcul=sum(float(row[k]) for k in noms)
        if abs(calcul-float(row['score']))>0.001:
            raise ValueError(f"Erreur de réconciliation des points à la partie {row.get('partie','?')}")
    tables={
        'points_par_clan': ['saisons','evenements','clan'],
        'points_par_clan_strategie': ['saisons','evenements','clan','strategie'],
        'points_par_clan_politique': ['saisons','evenements','clan','politique'],
    }
    out={}
    for nom,cles in tables.items():
        groupes=partition(lignes,cles)
        data=[]
        for key,rows in sorted(groupes.items()):
            n=len(rows)
            moyennes={col:round(sum(float(r[col]) for r in rows)/n,2) for col in noms}
            # Indicateurs globaux pour comparer la force des stratégies.
            moyennes.update(effectif=n,score_moyen=round(sum(float(r['score']) for r in rows)/n,2),
                            taux_victoire=round(100*sum(float(r['victoire']) for r in rows)/n,2))
            data.append({**dict(zip(cles,key)),**moyennes})
        fichier_csv(root/(nom+'.csv'),data)
        out[nom]=data
    return out


def graphe_decomposition_clans(rows,folder,saisons,events):
    """Une colonne colorée par clan : composition moyenne du score final."""
    if plt is None:return None
    relevant={r['clan']:r for r in rows if int(r['saisons'])==saisons and int(r['evenements'])==events}
    if not relevant:return None
    fig,ax=plt.subplots(figsize=(12,6))
    bas=np.zeros(len(CLANS));indices=np.arange(len(CLANS))
    for col,label,color in CHAMPS_POINTS:
        y=np.array([float(relevant.get(c,{}).get(col,0)) for c in CLANS])
        ax.bar(indices,y,bottom=bas,label=label,color=color,width=.77)
        bas+=y
    for i,clan in enumerate(CLANS):
        if clan in relevant:
            v=relevant[clan]
            ax.text(i,bas[i]+.6,f"{float(v['score_moyen']):.1f}  (n={v['effectif']})",ha='center',fontsize=7,rotation=35)
    ax.set_xticks(indices,[c.capitalize() for c in CLANS],rotation=22)
    ax.set_ylim(0,max(bas)*1.22+1)
    ax.set_ylabel('Points moyens par joueur')
    ax.set_title(f'Origine des points par clan — {saisons} saisons, événements {"oui" if events else "non"}')
    ax.legend(ncol=5,loc='upper center',bbox_to_anchor=(.5,-.13),fontsize=8,frameon=False)
    fig.tight_layout(rect=[0,.05,1,.97])
    name=f'points_par_clan_{saisons}_saisons_{"avec" if events else "sans"}_evenements.png'
    fig.savefig(folder/name,dpi=150);plt.close(fig)
    return name


def graphe_decomposition_strategies(rows,folder,saisons,events):
    """Huit petits graphiques : comparer les cinq stratégies de chaque clan."""
    if plt is None:return None
    lookup={(r['clan'],r['strategie']):r for r in rows if int(r['saisons'])==saisons and int(r['evenements'])==events}
    if not lookup:return None
    fig,axes=plt.subplots(4,2,figsize=(13,15),sharey=True)
    maxi=max(float(r['score_moyen']) for r in lookup.values())
    for idx,clan in enumerate(CLANS):
        ax=axes.flat[idx];bottom=np.zeros(5)
        for key,label,color in CHAMPS_POINTS:
            val=np.array([float(lookup.get((clan,strategie),{}).get(key,0)) for strategie in STRATEGIES])
            ax.bar(range(5),val,bottom=bottom,color=color,width=.79,label=label)
            bottom+=val
        for k,strat in enumerate(STRATEGIES):
            r=lookup.get((clan,strat))
            if r:
                ax.text(k,bottom[k]+.4,f"{bottom[k]:.1f}\nn={r['effectif']}",fontsize=7,ha='center')
        ax.set_xticks(range(5),['Survie','Chasse','Constr.','Explor.','Échanges'],rotation=25)
        ax.set_ylim(0,maxi*1.24+2)
        ax.set_title(clan.capitalize(),fontsize=11,fontweight='bold')
        ax.grid(axis='y',alpha=.14)
    from matplotlib.patches import Patch
    fig.legend(handles=[Patch(facecolor=c,label=label) for _,label,c in CHAMPS_POINTS],
               ncol=5,loc='lower center',bbox_to_anchor=(.5,.005),fontsize=8,frameon=False)
    fig.suptitle(f'Origine des points selon la stratégie — {saisons} saisons, événements {"oui" if events else "non"}',fontsize=15)
    fig.tight_layout(rect=[0,.045,1,.96],h_pad=2.1)
    name=f'points_par_clan_et_strategie_{saisons}_saisons_{"avec" if events else "sans"}_evenements.png'
    fig.savefig(folder/name,dpi=140);plt.close(fig)
    return name


def calculer_analyses(lignes,root):
    """Produit toutes les tables qui alimentent les graphiques et le rapport."""
    root=Path(root)
    tables={
        'par_clan_et_strategie':(['saisons','evenements','clan','strategie']),
        'par_clan':(['saisons','evenements','clan']),
        'par_strategie':(['saisons','evenements','strategie']),
        'par_politique_troc':(['saisons','evenements','politique']),
        'par_duree':(['saisons','evenements']),
        'par_clan_politique':(['saisons','evenements','clan','politique']),
    }
    resultat={}
    for nom,cles in tables.items():
        data=[]
        for key,rows in sorted(partition(lignes,cles).items()):
            data.append({**dict(zip(cles,key)),**agreger(rows)})
        resultat[nom]=data
        fichier_csv(root/(nom+'.csv'),data)
    # Tables complémentaires destinées à la lecture rapide des stratégies.
    resultat.update(analyser_decomposition(lignes,root))
    return resultat

def graphe_carte(table,folder,duree,events,metric,filename,titre,annotation=''):
    """Une case par clan et stratégie, avec nombre de observations en incrustation."""
    if plt is None:return None
    items={(r['clan'],r['strategie']):r for r in table if int(r['saisons'])==duree and int(r['evenements'])==events}
    data=np.array([[items.get((c,s),{}).get(metric,float('nan')) for s in STRATEGIES] for c in CLANS],dtype=float)
    fig,ax=plt.subplots(figsize=(11,5.6))
    im=ax.imshow(data,aspect='auto',cmap='YlGnBu')
    ax.set_xticks(range(len(STRATEGIES)),['Survie','Chasse','Construction','Exploration','Échanges'])
    ax.set_yticks(range(len(CLANS)),[c.capitalize() for c in CLANS])
    ax.set_title(titre,pad=16)
    for i,c in enumerate(CLANS):
        for j,s in enumerate(STRATEGIES):
            r=items.get((c,s))
            if r:
                text=f"{r[metric]:.1f}" if metric=='score_moyen' else f"{r[metric]:.1f}%"
                if r['effectif']<30:text+='*'
                ax.text(j,i,text+'\n'+f"n={r['effectif']}",ha='center',va='center',fontsize=8,
                        color='white' if data[i,j]>(np.nanmin(data)+np.nanmax(data))/2 else 'black')
    fig.colorbar(im,ax=ax,shrink=.77,label='Points moyens' if metric=='score_moyen' else 'Victoires (%)')
    fig.text(.02,.01,'* Effectif inférieur à 30 : prudence. '+annotation,fontsize=8,color='#444')
    fig.tight_layout(rect=[0,.04,1,1]);filename=str(folder/filename);fig.savefig(filename,dpi=150);plt.close(fig)
    return Path(filename).name

def graphe_plateau(folder):
    """Montre les 37 cases centrales et les quatre départs devant chaque joueur."""
    if plt is None:return None
    from matplotlib.patches import RegularPolygon,Rectangle
    fig,ax=plt.subplots(figsize=(8,8))
    ax.add_patch(Rectangle((-8.8,-8.8),17.6,17.6,facecolor='#e9d7b8',edgecolor='#8f7250',linewidth=3))
    for pos in COORDS:
        x,y=xy(pos)
        ax.add_patch(RegularPolygon((x,y),6,radius=0.98,orientation=math.pi/6,
                     facecolor='#e8e6d5',edgecolor='#8a8877',linewidth=1))
    colors=['#4b78a3','#c57945','#669c67','#a2608f']
    names=['Joueur 1 — haut','Joueur 2 — droite','Joueur 3 — bas','Joueur 4 — gauche']
    for i,pos in enumerate(SEATS):
        x,y=xy(pos)
        ax.add_patch(RegularPolygon((x,y),6,radius=0.98,orientation=math.pi/6,
                                    facecolor=colors[i],edgecolor='#47403b',linewidth=2))
        ax.text(x,y,str(i+1),ha='center',va='center',fontsize=15,fontweight='bold',color='white')
    ax.text(0,-8.2,names[0],ha='center',fontsize=11)
    ax.text(0,8.25,names[2],ha='center',fontsize=11)
    ax.text(6.4,0,names[1],ha='center',rotation=90,fontsize=11)
    ax.text(-6.6,0,names[3],ha='center',rotation=90,fontsize=11)
    ax.set_xlim(-8.9,8.9);ax.set_ylim(8.9,-8.9);ax.set_aspect('equal');ax.axis('off')
    ax.set_title('Table carrée — 37 tuiles centrales et 4 départs périphériques',fontsize=12,pad=20)
    fig.tight_layout();fig.savefig(folder/'disposition_quatre_joueurs.png',dpi=150);plt.close(fig)
    return 'disposition_quatre_joueurs.png'

def graphe_duree(table,folder):
    """Comparer uniquement les scénarios réellement présents dans le CSV."""
    if plt is None or not table:
        return None
    # Ne jamais afficher un scénario absent comme s'il obtenait un score de zéro.
    liste=sorted(table,key=lambda r:(int(r['saisons']),int(r['evenements'])))
    x=np.arange(len(liste))
    etiquettes=[f"{int(z['saisons'])} saisons\n{'Avec' if int(z['evenements']) else 'Sans'} événements"
                for z in liste]
    fig,axes=plt.subplots(2,1,figsize=(9,7))
    for ax,champ,titre in [(axes[0],'score_moyen','Score final moyen'),
                           (axes[1],'penuries_moyennes','Ressources manquantes par joueur')]:
        vals=[float(z[champ]) for z in liste]
        bars=ax.bar(x,vals,color=['#a5bdca','#377c9c','#cbd0a8','#6b9453'][:len(liste)])
        ax.set_xticks(x,etiquettes)
        ax.set_title(titre)
        for rect,valeur in zip(bars,vals):
            ax.text(rect.get_x()+rect.get_width()/2,rect.get_height(),f'{valeur:.1f}',
                    ha='center',va='bottom')
        ax.set_ylim(0,max(vals+[1])*1.20)
    fig.tight_layout()
    fig.savefig(folder/'comparaison_4_8_saisons.png',dpi=150)
    plt.close(fig)
    return 'comparaison_4_8_saisons.png'


def graphe_trocs(table,folder):
    """Comparer les politiques de troc même si un seul scénario a été sélectionné."""
    if plt is None or not table:
        return None
    # Privilégier les parties avec événements, sinon utiliser les parties sans.
    possible={int(z['evenements']) for z in table}
    ev=1 if 1 in possible else 0
    rows=[z for z in table if int(z['evenements'])==ev]
    durees=sorted({int(z['saisons']) for z in rows})
    if not durees:
        return None
    fig,ax=plt.subplots(figsize=(9,5))
    x=np.arange(len(POLITIQUES));largeur=0.75/len(durees)
    for i,d in enumerate(durees):
        trouve={z['politique']:z for z in rows if int(z['saisons'])==d}
        taux=[float(trouve.get(pol,{}).get('taux_victoire',0)) for pol in POLITIQUES]
        ax.bar(x+(i-(len(durees)-1)/2)*largeur,taux,largeur,label=f'{d} saisons')
    ax.axhline(25,linestyle='--',color='#666',linewidth=1,label='Référence : 25 %')
    ax.set_xticks(x,['Toujours','Jamais','Aléatoire','Si favorable'])
    ax.set_ylabel('Taux de victoire (%)')
    ax.set_title('Comportements de troc — '+('avec' if ev else 'sans')+' événements')
    ax.legend()
    fig.tight_layout()
    fig.savefig(folder/'comparaison_trocs.png',dpi=150)
    plt.close(fig)
    return 'comparaison_trocs.png'

def conseils_strategiques(table):
    """Formule un classement descriptif clan/durée, pas une stratégie assurée."""
    grouped=partition(table,['saisons','evenements','clan'])
    out=[]
    for (seasons,ev,clan),rows in sorted(grouped.items()):
        valid=[r for r in rows if r['effectif']>=30]
        if not valid:
            out.append(dict(saisons=seasons,evenements=ev,clan=clan,
                 strategie_recommandee='indéterminée',effectif=0,taux_victoire=0,
                 deuxieme_strategie='',ecart_points_pourcentage=0,confiance='échantillon insuffisant'))
            continue
        ordered=sorted(valid,key=lambda r:(r['taux_victoire'],r['score_moyen']),reverse=True)
        best=ordered[0]
        other=ordered[1] if len(ordered)>1 else None
        gap=round(best['taux_victoire']-other['taux_victoire'],2) if other else 0
        out.append(dict(saisons=seasons,evenements=ev,clan=clan,
             strategie_recommandee=best['strategie'],effectif=best['effectif'],
             taux_victoire=best['taux_victoire'],deuxieme_strategie=other['strategie'] if other else '',
             ecart_points_pourcentage=gap,
             confiance=('écart faible / incertain' if not other or gap <=best['marge_95_pts']+other['marge_95_pts']
                     else 'écart notable dans ce modèle')))
    return out

def generer_rapport(tableaux,folder,config,total_games,infos):
    """Enregistre graphiques, analyses et HTML entièrement dans le dossier choisi."""
    folder=Path(folder)
    graphs=[]
    board=graphe_plateau(folder)
    if board:graphs.append(board)
    for seasons in config['simulation']['saisons']:
        for event in config['simulation']['avec_evenements']:
            tag=f'{seasons}_saisons_'+('avec' if event else 'sans')+'_evenements'
            for field,label in [('taux_victoire','Taux de victoire'),('score_moyen','Score final moyen')]:
                f=graphe_carte(tableaux['par_clan_et_strategie'],folder,seasons,int(event),field,
                        f'strategies_{field}_{tag}.png',f'{label} par clan et stratégie — {seasons} saisons, événements {"oui" if event else "non"}')
                if f:graphs.append(f)
    # Nouveaux graphiques seulement si les CSV possèdent une décomposition exacte.
    if tableaux.get('points_par_clan') and tableaux.get('points_par_clan_strategie'):
        for saisons in config['simulation']['saisons']:
            for ev in config['simulation']['avec_evenements']:
                for image_name in (
                    graphe_decomposition_clans(tableaux['points_par_clan'],folder,saisons,int(ev)),
                    graphe_decomposition_strategies(tableaux['points_par_clan_strategie'],folder,saisons,int(ev)),
                ):
                    if image_name: graphs.append(image_name)
    for f in [graphe_duree(tableaux['par_duree'],folder),graphe_trocs(tableaux['par_politique_troc'],folder)]:
        if f:graphs.append(f)
    conseils=conseils_strategiques(tableaux['par_clan_et_strategie'])
    # Vue consolidée : additionne les parties avec/sans événements pour obtenir
    # des effectifs plus solides par clan sur 4 ou 8 saisons. Les conclusions
    # décrivent ce MÉLANGE de scénarios, et pas les seules parties avec cartes.
    pooled=[]
    with (folder/'resultats_par_joueur.csv').open(encoding='utf-8-sig',newline='') as file:
        from csv import DictReader
        source=list(DictReader(file))
    for (season,clan,strategy),rows in sorted(partition(source,['saisons','clan','strategie']).items()):
        pooled.append(dict(saisons=season,clan=clan,strategie=strategy,**agreger(rows)))
    fichier_csv(folder/'strategies_consolidees_avec_et_sans_evenements.csv',pooled)
    consolidated=[]
    for (season,clan),rows in sorted(partition(pooled,['saisons','clan']).items()):
        valid=[r for r in rows if r['effectif']>=30]
        if not valid:continue
        ranks=sorted(valid,key=lambda r:(r['taux_victoire'],r['score_moyen']),reverse=True)
        top=ranks[0]; runner=ranks[1] if len(ranks)>1 else None
        confidence='écart incertain' if (not runner or top['taux_victoire']-runner['taux_victoire']<=top['marge_95_pts']+runner['marge_95_pts']) else 'écart notable dans le modèle'
        consolidated.append(dict(saisons=season,clan=clan,strategie_en_tete=top['strategie'],
            taux_victoire=top['taux_victoire'],effectif=top['effectif'],
            deuxieme=runner['strategie'] if runner else '',confiance=confidence))
    fichier_csv(folder/'classement_consolide_par_clan.csv',consolidated)
    fichier_csv(folder/'meilleures_strategies_par_clan.csv',conseils)
    (folder/'interpretations.json').write_text(json.dumps(conseils,ensure_ascii=False,indent=2),encoding='utf-8')
    selected=[r for r in conseils if int(r['evenements'])==1]
    msg=[f'# AUROREA — Analyse de {total_games:,} parties simulées', '',
       f"Récompense du troc : {config['simulation']['points_par_troc']} point(s) par acceptation, plafonnée à {config['simulation']['maximum_points_troc_par_saison']} point(s) par saison.",
       '', '## Meilleures stratégies observées (événements activés)',
       '', '| Clans | Saisons | Stratégie en tête | Victoires | Effectif | Prudence |',
       '|---|---:|---|---:|---:|---|']
    for r in selected:
        msg.append(f"| {r['clan'].capitalize()} | {r['saisons']} | {r['strategie_recommandee']} | {r['taux_victoire']:.1f}% | {r['effectif']} | {r['confiance']} |")
    if tableaux.get('points_par_clan_strategie'):
        msg += ['', '## Origine des points par clan et stratégie',
          'Les tableaux points_par_clan.csv et points_par_clan_strategie.csv décrivent les points **restants en fin de partie** (et les bonus immédiats conservés), pas le total des ressources récoltées. La somme des catégories donne le score final. Les nourritures de départ et les bonus d’origine non définie restent non classés. La nourriture sans origine est consommée en premier, puis la végétale, puis l’animale : hypothèse du modèle.']
    else:
        msg += ['', '## Ventilation des points non disponible',
          'Le CSV provient d’une ancienne version qui ne suivait pas les origines des nourritures : relancer les parties avec V3 pour obtenir une ventilation exacte.']
    msg += ['', '## Conditions et limites importantes',
       '- Les résultats décrivent le **comportement de joueurs automatisés**, pas une expérience avec des humains.',
       '- Les stratégies sont des priorités de décision heuristiques et ne jouent pas toutes les actions de manière optimale.',
       '- La topologie comporte 37 tuiles hexagonales centrales et quatre tuiles de départ extérieures.',
       '- Les cartes Événements utilisent un corpus de travail et des effets immédiats simplifiés ; certains événements différés ne sont pas fidèlement reproduits.',
       '- Le déplacement, le placement par groupes, la construction, les malus et les échanges sont modélisés avec des approximations explicites.',
       '- Chaque joueur peut proposer des trocs à proximité d’un autre ; les ressources échangées sont de types différents.',
       '- Les scores additionnent ressources, anneaux, abris et gains immédiats ; les futures précisions de la règle peuvent modifier les conclusions.',
       '- Les taux de victoire sont des parts de victoire, les ex æquo étant partagés. Un taux élevé peut avoir une marge d’incertitude importante.',
       '- Le « meilleur » résultat est celui des cinq **stratégies testées**, pas nécessairement le meilleur style de jeu possible.',
       '- Une étoile sur un graphique signifie moins de 30 observations dans une case.',
       '- Le classement consolidé fusionne les parties avec et sans événements pour gagner en effectif, à interpréter seulement comme un classement de ce mélange.',
       '', '## Fichiers utiles',
       '- resultats_par_joueur.csv : inventaire, score et détail exact des catégories de points.',
       '- points_par_clan.csv : contribution moyenne de chaque catégorie, selon durée et événements.',
       '- points_par_clan_strategie.csv : même détail pour chacune des cinq stratégies de chaque clan.',
       '- points_par_clan_politique.csv : même détail selon la politique d’acceptation des trocs.',
       '- journal_des_trocs.csv : toutes les propositions de troc.',
       '- par_clan_et_strategie.csv : comparaisons clan × stratégie × durée × événements.',
       '- meilleures_strategies_par_clan.csv : classement descriptif.',
       '- classement_consolide_par_clan.csv : classement avec et sans événements regroupés.',
       '- parametres_utilises.json : réglages exactement sauvegardés avec le test.',
       '- interpretations.json : interprétations exploitables par un programme.',
       '', '### Modifications envisagées par rapport à la règle',
       '- Modifier la récompense des échanges et les avantages des clans se fait uniquement dans config_aurorea.json.',
       '- Une comparaison entre deux configurations demande de lancer deux expériences dans deux sous-dossiers indépendants.'
    ]
    (folder/'interpretation_statistique.md').write_text('\n'.join(msg),encoding='utf-8')
    # Rapport sans dépendance externe : lisible directement dans Chrome ou Edge.
    esc=lambda s:html.escape(str(s))
    rows=''.join('<tr>'+''.join(f'<td>{esc(r[k])}</td>' for k in
          ['clan','saisons','strategie_recommandee','taux_victoire','effectif','confiance'])+'</tr>' for r in selected)
    figs=''.join(f'<figure><img src="{esc(f)}"><figcaption>{esc(f)}</figcaption></figure>' for f in graphs)
    html_doc='''<!doctype html><html lang="fr"><head><meta charset="utf-8"><title>Aurorea — Rapport statistique</title>
    <style>body{font-family:Arial,sans-serif;max-width:1080px;margin:30px auto;padding:0 22px;color:#26343a}
    h1,h2{color:#225e68}table{border-collapse:collapse;width:100%}th,td{border-bottom:1px solid #ddd;padding:8px;text-align:left}
    th{background:#e6eff0}img{max-width:100%;height:auto}figure{margin:28px 0;padding:14px;border:1px solid #ddd;border-radius:10px}
    figcaption{color:#666;font-size:12px}aside{border-left:4px solid #cc974c;padding:10px 18px;background:#fff8e9}li{margin:8px 0}</style></head><body>'''
    html_doc+=f'<h1>Aurorea — {total_games} parties simulées</h1><p>Simulation probabiliste à quatre joueurs, huit clans et cinq stratégies.</p>'
    html_doc+=f'<p>Points par troc : {config["simulation"]["points_par_troc"]} ; plafond par saison : {config["simulation"]["maximum_points_troc_par_saison"]}.</p>'
    html_doc+='<aside>Les observations sont issues d’un modèle simplifié et ne prouvent pas l’équilibrage réel des clans.</aside>'
    html_doc+='<h2>Stratégies en tête selon le clan</h2><table><thead><tr><th>Clan</th><th>Saisons</th><th>Stratégie</th><th>Victoire %</th><th>Effectif</th><th>Fiabilité</th></tr></thead><tbody>'+rows+'</tbody></table>'
    cons_rows=''.join('<tr>'+''.join(f'<td>{esc(r[k])}</td>' for k in
          ['clan','saisons','strategie_en_tete','taux_victoire','effectif','confiance'])+'</tr>' for r in consolidated)
    html_doc+='<h2>Classement consolidé (avec et sans événements réunis)</h2><table><thead><tr><th>Clan</th><th>Saisons</th><th>Stratégie</th><th>Victoires %</th><th>Effectif</th><th>Fiabilité</th></tr></thead><tbody>'+cons_rows+'</tbody></table>'
    html_doc+='<h2>Graphiques</h2>'+figs+'<h2>Limites et fichiers produits</h2><ul>'
    html_doc+=''.join(f'<li>{esc(z[2:])}</li>' for z in msg if z.startswith('- '))
    html_doc+='</ul></body></html>'
    (folder/'rapport_statistique.html').write_text(html_doc,encoding='utf-8')
    return graphs

# ========= EXECUTION DES SIMULATIONS =========
tester_moteur = test

def nom_dossier_disponible(parent):
    """Évite d'écraser un résultat d'une précédente expérience."""
    root=Path(parent).expanduser().resolve()
    root.mkdir(parents=True,exist_ok=True)
    stamp=datetime.now().strftime('%Y%m%d_%H%M%S')
    out=root/f'experience_{stamp}'
    suffix=2
    while out.exists():
        out=root/f'experience_{stamp}_{suffix}'
        suffix+=1
    out.mkdir()
    return out

def executer(config,out_parent,progress=None):
    """Exécute exactement le nombre de parties demandé, tous scénarios confondus."""
    valider_configuration(config)
    tester_moteur()
    option=config['simulation']
    root=nom_dossier_disponible(out_parent)
    scenarios=[(int(d),bool(e)) for d in option['saisons'] for e in option['avec_evenements']]
    count=int(option['parties'])
    # La valeur 0 demande un nouveau tirage. La graine utilisée est conservée
    # dans les paramètres enregistrés, pour permettre une reproduction exacte.
    config=deepcopy(config)
    option=config['simulation']
    graine_demandee=int(option['graine'])
    graine_effective=(secrets.randbits(63) or 1) if graine_demandee==0 else graine_demandee
    option['graine']=graine_effective
    rng=random.Random(graine_effective)
    joueurs=[];trocs=[];traces=[]
    # Une distribution aussi équitable que possible, même si 1000/4 ne tombe pas juste.
    for i in range(count):
        seasons,events=scenarios[i%len(scenarios)]
        g=Game(random.Random(rng.getrandbits(64)),seasons,events,config=config)
        data=g.run()
        for row in data:
            joueurs.append(dict(partie=i+1,**row))
        for tr in g.tradelog:
            trocs.append(dict(partie=i+1,evenements=int(events),**tr))
        for tr in g.trace:
            traces.append(dict(partie=i+1,saisons=seasons,evenements=int(events),**tr))
        if progress and (i+1==count or (i+1)%max(1,count//20)==0):
            progress(i+1,count)
    fichier_csv(root/'resultats_par_joueur.csv',joueurs)
    fichier_csv(root/'journal_des_trocs.csv',trocs)
    fichier_csv(root/'evolution_scores.csv',traces)
    (root/'parametres_utilises.json').write_text(json.dumps(config,ensure_ascii=False,indent=2),encoding='utf-8')
    # IMPORTANT : arrêt du calcul ici. Les CSV sont disponibles pour le bouton PDF.
    summary=dict(parties=count,graine_demandee=graine_demandee,graine_utilisee=graine_effective,observations=len(joueurs),propositions_troc=len(trocs),
                 scenarios=[dict(saisons=s,avec_evenements=e) for s,e in scenarios],
                 strategies=STRATEGIES,graphiques=0,dossier=str(root))
    (root/'resume_execution.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2),encoding='utf-8')
    return summary


# ========= RAPPORT PDF AUTONOME, À PARTIR DES CSV =========

def lire_csv(chemin):
    """Lit un tableau CSV Windows/Excel, y compris avec marqueur BOM UTF-8."""
    with Path(chemin).open('r', encoding='utf-8-sig', newline='') as fichier:
        return list(csv.DictReader(fichier))


def generer_pdf_complet(dossier, graphiques, config, joueurs):
    """Assemble un PDF imprimable de plusieurs pages avec tous les graphiques.

    Les CSV font foi : on n'invente pas de résultats à partir d'images existantes.
    Les graphiques sont recalculés avant d'appeler cette fonction.
    """
    # ReportLab est chargé ici : les simulations CSV peuvent fonctionner sans lui.
    try:
        from reportlab.lib import colors
        from reportlab.lib.enums import TA_CENTER, TA_LEFT
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
        from reportlab.lib.utils import ImageReader
        from reportlab.pdfbase import pdfmetrics
        from reportlab.pdfbase.ttfonts import TTFont
        from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer,
                                        Table, TableStyle, PageBreak, Image as PDFImage,
                                        KeepTogether, HRFlowable)
    except ImportError as exc:
        raise RuntimeError('ReportLab manque : installez-le avec « py -m pip install reportlab ».') from exc

    # Le PDF est enregistré dans le même dossier que les résultats et interprétations.
    dossier = Path(dossier).expanduser().resolve()
    destination = dossier / 'Rapport_complet_Aurorea.pdf'
    report_data = calculer_analyses(joueurs, dossier)
    n_parties = len({r['partie'] for r in joueurs})
    scenarios = sorted({(int(r['saisons']), int(r['evenements'])) for r in joueurs})
    datestr = datetime.now().strftime('%d/%m/%Y à %H:%M')

    # Les polices sont choisies localement, sans joindre de fichier de police.
    # Arial sous Windows et DejaVu sous Linux gèrent les accents français.
    polices = [
        (Path('C:/Windows/Fonts/arial.ttf'), Path('C:/Windows/Fonts/arialbd.ttf')),
        (Path('/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf'),
         Path('/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf')),
    ]
    font, boldfont = 'Helvetica', 'Helvetica-Bold'
    for normal, gras in polices:
        if normal.is_file() and gras.is_file():
            try:
                pdfmetrics.registerFont(TTFont('Aurorea-Regular', str(normal)))
                pdfmetrics.registerFont(TTFont('Aurorea-Bold', str(gras)))
                font, boldfont = 'Aurorea-Regular', 'Aurorea-Bold'
                break
            except Exception:
                continue

    # Feuille A4 et marges généreuses pour permettre l'impression.
    doc = SimpleDocTemplate(str(destination), pagesize=A4, leftMargin=43,
                            rightMargin=43, topMargin=57, bottomMargin=49,
                            title=f'Aurorea - {n_parties} simulations',
                            author='Simulateur Aurorea - analyse expérimentale')
    w, h = A4
    bleu = colors.HexColor('#1f5863')
    clair = colors.HexColor('#eaf2f3')
    texte = colors.HexColor('#243238')
    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle(name='AurTitre', fontName=boldfont, fontSize=25,
                 leading=30, textColor=bleu, spaceAfter=12))
    styles.add(ParagraphStyle(name='AurH1', fontName=boldfont, fontSize=16,
                 leading=20, textColor=bleu, spaceBefore=10, spaceAfter=9))
    styles.add(ParagraphStyle(name='AurH2', fontName=boldfont, fontSize=12,
                 leading=16, textColor=bleu, spaceBefore=9, spaceAfter=5))
    styles.add(ParagraphStyle(name='AurTexte', fontName=font, fontSize=9.2,
                 leading=14.2, textColor=texte, spaceAfter=7))
    styles.add(ParagraphStyle(name='AurPetite', fontName=font, fontSize=7.7,
                 leading=10.7, textColor=texte, spaceAfter=4))
    styles.add(ParagraphStyle(name='AurTh', fontName=boldfont, fontSize=7.6,
                 leading=10.6, textColor=bleu))
    styles.add(ParagraphStyle(name='AurTd', fontName=font, fontSize=7.4,
                 leading=10.2, textColor=texte))
    styles.add(ParagraphStyle(name='AurSousTitre', fontName=font, fontSize=11,
                 leading=16, textColor=texte, spaceAfter=14))

    # L'échappement empêche les signes présents dans les CSV d'être traités comme HTML.
    p = lambda value, sty='AurTexte': Paragraph(saxutils.escape(str(value)), styles[sty])
    story = []
    story.append(Spacer(1, 38))
    story.append(p('AUROREA', 'AurTitre'))
    story.append(p('Étude statistique et comparaison des stratégies', 'AurSousTitre'))
    story.append(HRFlowable(width='100%', thickness=2, color=bleu, spaceAfter=22))
    story.append(p(f'{n_parties:,} parties simulées - {len(joueurs):,} résultats individuels.'))
    story.append(p('Quatre joueurs placés autour du plateau ; huit clans ; cinq styles de jeu ; '
                   'quatre comportements de troc.'))
    story.append(p(f'Rapport généré le {datestr}.'))
    opts = config['simulation']
    story.append(p(f"Graine utilisée : {opts['graine']} (0 dans le champ de saisie tire une nouvelle graine)."))
    story.append(p(f"Bonus par troc accepté : {opts['points_par_troc']} point(s). "
                   f"Plafond par saison : {opts['maximum_points_troc_par_saison']} point(s)."))
    story.append(Spacer(1, 12))
    story.append(p('IMPORTANT : ces chiffres proviennent d’un modèle de joueurs virtuels. '
                   'Ils ne constituent pas une validation de l’équilibrage réel du jeu.'))
    story.append(p('Le PDF et tous les graphiques sont reconstruits à partir des CSV du dossier '
                   'sélectionné, sans relancer les parties.'))
    story.append(PageBreak())

    def tableau(headers, values, widths=None):
        """Fabrique un tableau avec titres répétés après un changement de page."""
        rows = [[p(t, 'AurTh') for t in headers]]
        rows += [[p(v, 'AurTd') for v in row] for row in values]
        t = Table(rows, colWidths=widths, repeatRows=1, hAlign='LEFT')
        t.setStyle(TableStyle([
            ('BACKGROUND', (0,0), (-1,0), clair),
            ('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white,colors.HexColor('#f6f9f9')]),
            ('VALIGN',(0,0),(-1,-1),'TOP'),
            ('LINEBELOW',(0,0),(-1,0),0.7,bleu),
            ('BOTTOMPADDING',(0,0),(-1,-1),7),
            ('TOPPADDING',(0,0),(-1,-1),6),
            ('LEFTPADDING',(0,0),(-1,-1),6),
            ('RIGHTPADDING',(0,0),(-1,-1),6),
        ]))
        return t

    # Vue générale : scénarios courts / longs et avec / sans événements.
    story.append(p('1. Résultats généraux', 'AurH1'))
    story.append(p('Chaque ligne résume les résultats individuels correspondant au scénario. '
                   'Les moyennes de pénuries et d’anneaux perdus représentent des difficultés '
                   'accumulées sur toute la partie.'))
    dur = {(int(z['saisons']), int(z['evenements'])):z
           for z in report_data['par_duree']}
    rows = []
    for (s,ev), a in sorted(dur.items()):
        rows.append([str(s), 'Avec' if ev else 'Sans', str(a['effectif']),
                     f"{a['score_moyen']:.1f}", f"{a['penuries_moyennes']:.1f}",
                     f"{a['anneaux_perdus_moyens']:.1f}", f"{a['grottes_pct']:.1f} %"])
    story.append(tableau(['Saisons','Événements','Joueurs','Score moy.','Pénuries',
                         'Anneaux perdus','Grottes'], rows,
                         widths=[58,73,60,75,75,79,58]))
    story.append(Spacer(1, 14))
    story.append(p('2. Trocs : les quatre comportements', 'AurH1'))
    story.append(p('Un joueur « favorable » accepte seulement lorsque le modèle estime '
                   'l’échange profitable. Cette estimation est une heuristique, pas une règle.'))
    lignes=[]
    for z in sorted(report_data['par_politique_troc'],
                    key=lambda a:(int(a['saisons']),int(a['evenements']),a['politique'])):
        lignes.append([str(z['saisons']), 'Oui' if int(z['evenements']) else 'Non',
                      z['politique'],str(z['effectif']),
                      f"{z['taux_victoire']:.1f} %",f"{z['trocs_acceptes_moyens']:.2f}",
                      f"{z['bonus_troc_moyen']:.2f}"])
    story.append(tableau(['Saisons','Évént.','Politique','N','Victoires',
                         'Trocs moy.','Bonus moy.'],lignes,
                         widths=[57,57,90,40,89,74,71]))
    story.append(Spacer(1, 13))
    story.append(p('Les taux de victoire sont des parts de victoire : les égalités sont partagées. '
                   'Pour tirer une conclusion, il faut aussi regarder l’effectif de chaque groupe.',
                   'AurPetite'))

    # La comparaison des stratégies doit présenter les huit clans, y compris les cas indéterminés.
    story.append(PageBreak())
    story.append(p('3. Quelles stratégies semblent convenir aux clans ?', 'AurH1'))
    story.append(p('Le classement mesure uniquement les stratégies automatisées testées. '
                   'Une stratégie classée première sur un petit effectif n’est pas nécessairement '
                   'meilleure dans une partie réelle.'))
    recommandations = conseils_strategiques(report_data['par_clan_et_strategie'])
    for saisons, ev in scenarios:
        story.append(p(f'{saisons} saisons - événements {"activés" if ev else "désactivés"}', 'AurH2'))
        best = [r for r in recommandations if int(r['saisons'])==saisons and int(r['evenements'])==ev]
        best.sort(key=lambda x:x['clan'])
        data=[]
        for r in best:
            data.append([r['clan'].capitalize(),r['strategie_recommandee'],
                        f"{r['taux_victoire']:.1f} %" if r['effectif'] else '—',
                        str(r['effectif']),r['confiance']])
        story.append(tableau(['Clan','En tête','Victoires','N','Prudence'],data,
                             widths=[77,105,73,47,176]))
        story.append(Spacer(1, 14))
    story.append(p('« Indéterminée » signifie qu’aucune des cinq stratégies n’a atteint '
                   'le seuil indicatif de 30 observations pour ce clan et ce scénario.',
                   'AurPetite'))

    # La vue consolidée contient davantage de parties, mais mélange deux conditions.
    consolidate = dossier/'classement_consolide_par_clan.csv'
    if consolidate.exists():
        data = lire_csv(consolidate)
        if data and 'strategie_en_tete' in data[0]:
            story.append(PageBreak())
            story.append(p('4. Synthèse par clan, scénarios réunis', 'AurH1'))
            story.append(p('Les parties avec et sans événements sont réunies pour augmenter '
                           'les effectifs. Cette synthèse ne décrit donc aucun des deux scénarios seul.'))
            rows=[[z['clan'].capitalize(),z['saisons'],z['strategie_en_tete'],
                   f"{float(z['taux_victoire']):.1f} %",z['effectif'],z['confiance']]
                  for z in data]
            story.append(tableau(['Clan','Saisons','Stratégie','Victoires','N','Fiabilité'],
                                 rows,widths=[70,58,93,75,47,135]))

    # Décomposition : les valeurs du tableau sont des MOYENNES, pas des totaux.
    # N'afficher cette section que si le CSV possède toutes les colonnes fiables.
    detail=report_data.get('points_par_clan',[])
    details_strategies=report_data.get('points_par_clan_strategie',[])
    story.append(PageBreak())
    story.append(p('5. Origine moyenne des points par clan', 'AurH1'))
    if not detail:
        story.append(p('Ventilation indisponible : ces CSV ont été créés avec une version antérieure '
                       'qui ne distinguait pas les nourritures animales et végétales. '
                       'Relancez une simulation avec cette version pour obtenir les données exactes.'))
    else:
        story.append(p('Chaque moyenne représente les points effectivement conservés à la fin. '
                       'Les consommations et pertes de ressources sont déjà déduites. '
                       'La nourriture d’origine non précisée est affichée séparément. '
                       'Le total des catégories est égal au score final, à l’arrondi près.'))
        for saisons,ev in scenarios:
            story.append(p(f'{saisons} saisons - événements {"activés" if ev else "désactivés"}', 'AurH2'))
            scenario=[z for z in detail if int(z['saisons'])==saisons and int(z['evenements'])==ev]
            # Tableau condensé : deux groupes de colonnes pour rester lisible en A4.
            first=[];second=[]
            for z in sorted(scenario,key=lambda r:r['clan']):
                nom=z['clan'].capitalize()
                first.append([nom,str(z['effectif']),f"{z['score_moyen']:.1f}",
                              f"{z['points_grottes']:.1f}",f"{z['points_huttes']:.1f}",
                              f"{z['points_trocs']:.1f}",f"{z['points_explorations']:.1f}"])
                second.append([nom,f"{z['points_nourriture_animale']:.1f}",
                        f"{z['points_nourriture_vegetale']:.1f}",
                        f"{z['points_nourriture_non_classee']:.1f}",
                        f"{z['points_autres_ressources']:.1f}",f"{z['points_anneaux']:.1f}"])
            story.append(tableau(['Clan','N','Score','Grottes','Huttes','Trocs','Explor.'],first,
                                 widths=[92,44,70,72,72,65,65]))
            story.append(Spacer(1,5))
            story.append(tableau(['Clan','Animale','Végétale','Non classée','Autres ress.','Anneaux'],second,
                                 widths=[92,79,79,86,100,65]))
            # Le détail des cinq stratégies de chaque clan est inclus dans les CSV
            # et dans les graphiques « points_par_clan_et_strategie ».
            scenario_strat=[z for z in details_strategies if int(z['saisons'])==saisons and int(z['evenements'])==ev]
            winners=[]
            for nom in CLANS:
                options=[z for z in scenario_strat if z['clan']==nom]
                if options:
                    # Ce classement par score complète celui par taux de victoire.
                    top=max(options,key=lambda z:(z['score_moyen'],z['taux_victoire']))
                    winners.append([nom.capitalize(),top['strategie'],f"{top['score_moyen']:.1f}",
                                    str(top['effectif'])])
            story.append(Spacer(1,7))
            story.append(p('Stratégie offrant le meilleur score moyen (dans cette série ; effectifs faibles à interpréter avec prudence)', 'AurPetite'))
            story.append(tableau(['Clan','Stratégie en tête','Points moyens','Effectif'],winners,
                                 widths=[104,173,115,110]))
            story.append(Spacer(1,15))
        story.append(p('Ces classements décrivent la simulation, pas une stratégie universelle. '
                       'Les résultats par politique de troc et par stratégie sont disponibles '
                       'dans les CSV détaillés.', 'AurPetite'))

    # Chaque figure bénéficie de sa propre page, ce qui évite les légendes rognées.
    story.append(PageBreak())
    story.append(p('6. Graphiques détaillés', 'AurH1'))
    story.append(p('Les cartes de chaleur comparent les clans et les styles de jeu. '
                   'Une étoile signale généralement moins de 30 observations. '
                   'Des écarts faibles ne doivent pas être surinterprétés.'))
    for nom in graphiques:
        chemin=dossier/nom
        if not chemin.is_file():
            continue
        # Insérer une page réservée par figure, en conservant les proportions de l'image.
        story.append(PageBreak())
        description=(nom.replace('strategies_taux_victoire','Victoires par clan et stratégie')
                       .replace('strategies_score_moyen','Score par clan et stratégie')
                       .replace('comparaison_4_8_saisons','Comparaison des deux durées')
                       .replace('comparaison_trocs','Comparaison des comportements de troc')
                       .replace('disposition_quatre_joueurs','Disposition de la table')
                       .replace('points_par_clan_et_strategie','Composition des points par stratégie et clan')
                       .replace('points_par_clan','Composition moyenne des points par clan')
                       .replace('_',' ').replace('.png',''))
        story.append(p(description[:100], 'AurH2'))
        img=ImageReader(str(chemin))
        iw,ih=img.getSize()
        # Limiter la taille de l'image au cadre imprimable.
        ratio=min((w-94)/iw, (h-175)/ih)
        story.append(PDFImage(str(chemin), width=iw*ratio, height=ih*ratio))
        story.append(Spacer(1,10))
        story.append(p('Source : données CSV de cette expérience. '
                       'Résultats du simulateur, non résultats de parties humaines.',
                       'AurPetite'))

    story.append(PageBreak())
    story.append(p('7. Méthode et limites de cette étude', 'AurH1'))
    limites=[
       'Les acteurs virtuels suivent cinq règles de priorité : survie, chasse, construction, '
       'exploration, échanges. Leur comportement n’est ni humain ni nécessairement optimal.',
       'Les 37 tuiles hexagonales centrales et les quatre tuiles de départ sont représentées. '
       'La disposition spatiale peut influer sur les possibilités des clans.',
       'Certaines cartes Événements ont été adaptées ou simplifiées, notamment les effets '
       'différés. Les conclusions changeraient si les règles des événements changeaient.',
       'La gestion des déplacements groupés, trocs, pénalités, constructions et récoltes '
       'repose sur des hypothèses explicites du simulateur v2.',
       'La réussite d’une chasse utilise des dés simulés ; les pénuries et bonus dépendent '
       'également des choix programmés.',
       'Une association statistique ne prouve pas un avantage réel. Les taux de victoire '
       'dépendent des adversaires, du tirage des clans, des événements et des stratégies.',
       'L’erreur approximative affichée dans les tableaux statistiques est indicative. '
       'Les observations de joueurs d’une même partie ne sont pas indépendantes.',
       'La ventilation du score attribue une origine aux nourritures quand elle est connue. '
       'Les nourritures initiales et les bonus non explicités restent non classés. '
       'La consommation retire d’abord les aliments non classés, puis végétaux, puis animaux.',
       'Les résultats servent à préparer des essais avec de vrais joueurs, pas à modifier '
       'définitivement la règle sans vérification.',
    ]
    for i,t in enumerate(limites,1):
        story.append(p(f'{i}. {t}'))
    story.append(p('8. Fichiers fournis avec cette expérience', 'AurH1'))
    for item in ('resultats_par_joueur.csv : détails individuels de chaque partie',
                 'journal_des_trocs.csv : offres et réponses des joueurs virtuels',
                 'evolution_scores.csv : évolution des ressources et scores',
                 'par_clan_et_strategie.csv : statistiques par clan, durée et contexte',
                 'meilleures_strategies_par_clan.csv : classement par conditions de jeu',
                 'interpretation_statistique.md : synthèse textuelle et réserves',
                 'points_par_clan.csv : moyennes par catégorie et par clan',
                 'points_par_clan_strategie.csv : ventilation selon chaque stratégie',
                 'points_par_clan_politique.csv : ventilation selon les choix de troc',
                 'parametres_utilises.json : paramètres et graine effectivement utilisés'):
        story.append(p('• '+item, 'AurPetite'))

    def en_tete_bas_page(canvas, document):
        """Dessine des repères constants, hors du contenu de chaque page."""
        canvas.saveState()
        canvas.setStrokeColor(colors.HexColor('#b9d0d2'))
        canvas.line(43,h-41,w-43,h-41)
        canvas.setFont(font,7.5)
        canvas.setFillColor(bleu)
        canvas.drawString(43,h-34,'AUROREA   |   Laboratoire de simulation')
        canvas.setFillColor(colors.HexColor('#65777d'))
        canvas.drawString(43,32,'Statistiques expérimentales - ne remplacent pas les tests réels')
        canvas.drawRightString(w-43,32,f'Page {document.page}')
        canvas.restoreState()

    # build(...) écrit le PDF sur disque ; une exception ne doit jamais annoncer un succès.
    doc.build(story,onFirstPage=en_tete_bas_page,onLaterPages=en_tete_bas_page)
    return destination


def rapport_depuis_csv(dossier, progression=None):
    """Recrée interprétations, graphiques puis PDF SANS refaire les simulations."""
    dossier=Path(dossier).expanduser().resolve()
    fichier=dossier/'resultats_par_joueur.csv'
    if not fichier.is_file():
        raise FileNotFoundError('Impossible de trouver « resultats_par_joueur.csv » dans ce dossier.')
    if plt is None or np is None:
        raise RuntimeError('Pour les graphiques : py -m pip install matplotlib numpy')
    # Les résultats CSV restent les mêmes pendant toute la génération du rapport.
    lignes=lire_csv(fichier)
    if not lignes:
        raise ValueError('Le CSV des résultats est vide.')
    champs={'partie','saisons','evenements','clan','strategie','politique','score',
            'victoire','penuries','anneaux_perdus','explorations','grandes_chasses',
            'hutte','grotte','trocs_acceptes','bonus_troc'}
    manquants=champs-set(lignes[0])
    if manquants:
        raise ValueError('Le CSV ne contient pas les colonnes nécessaires : '+', '.join(sorted(manquants)))
    # Récupérer en priorité les paramètres propres à cette expérience.
    chemin_params=dossier/'parametres_utilises.json'
    if chemin_params.exists():
        config=charger_configuration(chemin_params)
    else:
        # Un ancien CSV n'a parfois pas de JSON. L'utilisateur en est informé.
        config=configuration_defaut()
        # Sans paramètres sauvegardés, la graine passée n'est pas vérifiable.
        config['simulation']['graine']='non enregistrée (ancien CSV)'
    n=len({z['partie'] for z in lignes})
    if progression: progression('Calcul des tableaux statistiques…')
    tables=calculer_analyses(lignes,dossier)
    # La liste des scénarios provient ici des résultats réellement présents.
    config=deepcopy(config)
    config['simulation']['saisons']=sorted({int(z['saisons']) for z in lignes})
    config['simulation']['avec_evenements']=sorted({bool(int(z['evenements'])) for z in lignes})
    if progression: progression('Création des graphiques et interprétations…')
    graphiques=generer_rapport(tables,dossier,config,n,{'sièges':SEATS})
    if progression: progression('Assemblage du rapport PDF…')
    pdf=generer_pdf_complet(dossier,graphiques,config,lignes)
    # Écrire un état récapitulatif pour identifier le rapport sans ouvrir le PDF.
    resume=dict(parties=n,observations=len(lignes),graphiques=len(graphiques),
                fichier_pdf=str(pdf),dossier=str(dossier))
    (dossier/'resume_execution.json').write_text(json.dumps(resume,ensure_ascii=False,indent=2),
                                                  encoding='utf-8')
    return resume

# ========= INTERFACE WINDOWS : UN SEUL FICHIER .PY =========
class InterfaceAurorea(tk.Tk):
    """Fenêtre centrale : exécution, édition des clans et création du PDF à la demande."""

    def __init__(self):
        super().__init__()
        self.title('AUROREA V3 - Simulations et rapport PDF (tout-en-un)')
        self.geometry('870x735')
        self.minsize(780,660)
        # Préférer le fichier JSON local seulement s'il existe déjà et est valide.
        local_config=HOME/'config_aurorea.json'
        try:
            self.config_data=(charger_configuration(local_config) if local_config.is_file()
                              else configuration_defaut())
        except Exception:
            self.config_data=configuration_defaut()
        self.config_path=local_config
        sim=self.config_data['simulation']
        # StringVar maintient la fenêtre synchronisée avec les champs affichés.
        self.output_parent=tk.StringVar(value=str(HOME/'Statistiques_Aurorea'))
        self.experience=tk.StringVar(value='')
        self.parties=tk.StringVar(value=str(sim['parties']))
        self.graine=tk.StringVar(value=str(sim['graine']))
        self.troc=tk.StringVar(value=str(sim['points_par_troc']))
        self.plafond=tk.StringVar(value=str(sim['maximum_points_troc_par_saison']))
        self.offres=tk.StringVar(value=str(sim['maximum_offres_par_tour']))
        self.proba=tk.StringVar(value=str(sim['probabilite_troc_aleatoire']))
        self.durees={s:tk.BooleanVar(value=s in sim['saisons']) for s in (4,8)}
        self.events={v:tk.BooleanVar(value=v in sim['avec_evenements']) for v in (False,True)}
        self.statut=tk.StringVar(value='Prêt. Choisissez un dossier, puis lancez les simulations.')
        self.active=False
        self._widgets()

    def _widgets(self):
        """Construire les contrôles Tkinter, sans fichier d'interface externe."""
        panel=ttk.Frame(self,padding=16)
        panel.pack(fill='both',expand=True)
        ttk.Label(panel,text='AUROREA - LABORATOIRE STATISTIQUE',
                  font=('Segoe UI',16,'bold')).pack(anchor='w')
        ttk.Label(panel,text='4 joueurs, 8 clans, 5 stratégies, 4 comportements de troc',
                  font=('Segoe UI',10)).pack(anchor='w',pady=(2,12))

        sortie=ttk.LabelFrame(panel,text='1. Où enregistrer les expériences ?',padding=10)
        sortie.pack(fill='x',pady=5)
        ttk.Entry(sortie,textvariable=self.output_parent).pack(side='left',fill='x',expand=True)
        ttk.Button(sortie,text='Parcourir…',command=self.parcourir_parent).pack(side='left',padx=(8,0))
        ttk.Label(panel,text='Chaque simulation crée son propre sous-dossier : CSV, graphiques, PDF et interprétations.',
                  wraplength=810).pack(anchor='w',pady=(0,8))

        options=ttk.LabelFrame(panel,text='2. Paramètres et scénarios',padding=10)
        options.pack(fill='x',pady=5)
        fields=[('Nombre de parties',self.parties),('Graine (0 = nouvelle graine aléatoire)',self.graine),
                ('Points par troc accepté',self.troc),('Bonus troc maximum / saison',self.plafond),
                ('Offres maximum / tour',self.offres),('Probabilité acceptation aléatoire',self.proba)]
        for i,(label,var) in enumerate(fields):
            ttk.Label(options,text=label).grid(row=i,column=0,sticky='w',pady=4,padx=5)
            ttk.Entry(options,textvariable=var,width=15).grid(row=i,column=1,sticky='w',pady=4,padx=8)
        ttk.Label(options,text='Durée des parties',font=('Segoe UI',9,'bold')).grid(
            row=0,column=2,sticky='w',padx=(26,5))
        for i,s in enumerate((4,8),1):
            ttk.Checkbutton(options,text=f'{s} saisons',variable=self.durees[s]).grid(
                row=i,column=2,sticky='w',padx=(26,5))
        ttk.Label(options,text='Cartes Événements',font=('Segoe UI',9,'bold')).grid(
            row=3,column=2,sticky='w',padx=(26,5))
        ttk.Checkbutton(options,text='Sans événements',variable=self.events[False]).grid(
            row=4,column=2,sticky='w',padx=(26,5))
        ttk.Checkbutton(options,text='Avec événements',variable=self.events[True]).grid(
            row=5,column=2,sticky='w',padx=(26,5))

        configrow=ttk.Frame(panel)
        configrow.pack(fill='x',pady=9)
        ttk.Button(configrow,text='Modifier les 8 clans…',command=self.editer_clans).pack(side='left',padx=3)
        ttk.Button(configrow,text='Charger paramètres JSON…',command=self.charger_json).pack(side='left',padx=3)
        ttk.Button(configrow,text='Enregistrer paramètres JSON…',command=self.enregistrer_json).pack(side='left',padx=3)

        production=ttk.LabelFrame(panel,text='3. Lancer, puis générer le rapport PDF',padding=10)
        production.pack(fill='x',pady=5)
        buttons=ttk.Frame(production)
        buttons.pack(fill='x',pady=(2,8))
        self.btn_sim=ttk.Button(buttons,text='LANCER LES SIMULATIONS',command=self.lancer)
        self.btn_sim.pack(side='left',padx=(0,7))
        self.btn_pdf=ttk.Button(buttons,text='GÉNÉRER LE RAPPORT PDF',command=self.rapport_pdf,state='disabled')
        self.btn_pdf.pack(side='left',padx=7)
        self.btn_exist=ttk.Button(buttons,text='Ouvrir des CSV existants…',command=self.csv_existants)
        self.btn_exist.pack(side='left',padx=7)
        ttk.Label(production,text='Dossier de l’expérience qui sera analysée :').pack(anchor='w')
        ttk.Entry(production,textvariable=self.experience,state='readonly').pack(fill='x',pady=(3,9))
        self.progress=ttk.Progressbar(production,mode='determinate',maximum=100)
        self.progress.pack(fill='x',pady=(0,5))
        ttk.Label(production,textvariable=self.statut,wraplength=810).pack(anchor='w')
        ttk.Label(panel,text='Le bouton PDF analyse les CSV déjà présents : aucune partie n’est rejouée.',
                  wraplength=800).pack(anchor='w',pady=10)

    def parcourir_parent(self):
        chemin=filedialog.askdirectory(title='Dossier parent de toutes les expériences',
                                       initialdir=str(HOME))
        if chemin:
            self.output_parent.set(chemin)

    def csv_existants(self):
        """Permet de refaire le PDF d'un ancien calcul après redémarrage du PC."""
        chemin=filedialog.askdirectory(title='Choisir un dossier contenant resultats_par_joueur.csv',
                                       initialdir=self.output_parent.get())
        if chemin:
            self.experience.set(chemin)
            if not (Path(chemin)/'resultats_par_joueur.csv').is_file():
                messagebox.showwarning('CSV absent',
                                       'Ce dossier ne contient pas resultats_par_joueur.csv.')
            self._activer_pdf_si_csv()

    def _activer_pdf_si_csv(self):
        # Ce bouton n'est actif que si un véritable fichier CSV existe.
        valide=(not self.active and
                (Path(self.experience.get())/'resultats_par_joueur.csv').is_file())
        self.btn_pdf.config(state='normal' if valide else 'disabled')

    def lire_reglages(self):
        """Lire et valider toutes les options avant le lancement des parties."""
        cfg=deepcopy(self.config_data)
        s=cfg['simulation']
        s.update(parties=int(self.parties.get()),graine=int(self.graine.get()),
                 points_par_troc=int(self.troc.get()),
                 maximum_points_troc_par_saison=int(self.plafond.get()),
                 maximum_offres_par_tour=int(self.offres.get()),
                 probabilite_troc_aleatoire=float(self.proba.get().replace(',','.')),
                 saisons=[n for n,v in self.durees.items() if v.get()],
                 avec_evenements=[v for v,sel in self.events.items() if sel.get()])
        valider_configuration(cfg)
        if not self.output_parent.get().strip():
            raise ValueError('Sélectionnez un répertoire pour les fichiers résultats.')
        return cfg

    def afficher_reglages(self,cfg):
        # Charger dans la fenêtre les valeurs d'un JSON existant.
        self.config_data=cfg
        s=cfg['simulation']
        for key,var in (('parties',self.parties),('graine',self.graine),
                        ('points_par_troc',self.troc),
                        ('maximum_points_troc_par_saison',self.plafond),
                        ('maximum_offres_par_tour',self.offres),
                        ('probabilite_troc_aleatoire',self.proba)):
            var.set(str(s[key]))
        for duree,v in self.durees.items():v.set(duree in s['saisons'])
        for ev,v in self.events.items():v.set(ev in s['avec_evenements'])

    def charger_json(self):
        fichier=filedialog.askopenfilename(title='Paramètres Aurorea',
                                           filetypes=[('JSON','*.json')])
        if fichier:
            try:
                self.afficher_reglages(charger_configuration(fichier))
                self.config_path=Path(fichier)
            except Exception as exc:
                messagebox.showerror('Impossible de charger le fichier',str(exc))

    def enregistrer_json(self):
        try:
            cfg=self.lire_reglages()
        except Exception as exc:
            messagebox.showerror('Paramètres non valides',str(exc))
            return
        fichier=filedialog.asksaveasfilename(defaultextension='.json',
                     initialfile='config_aurorea.json',filetypes=[('JSON','*.json')])
        if fichier:
            sauvegarder_configuration(fichier,cfg)
            self.config_path=Path(fichier)
            self.config_data=cfg

    def editer_clans(self):
        """Éditeur JSON intégré des forces et faiblesses, sans deuxième programme."""
        fen=tk.Toplevel(self)
        fen.title('Paramètres des huit clans Aurorea')
        fen.geometry('910x650')
        fen.transient(self)
        fen.grab_set()
        panel=ttk.Frame(fen,padding=10)
        panel.pack(fill='both',expand=True)
        ttk.Label(panel,text='Choisissez un clan. Éditez ses paramètres JSON ci-dessous : '
                  'true/false pour les effets, nombres pour les bonus.',wraplength=840).pack(anchor='w')
        noms=list(self.config_data['clans'])
        current=[noms[0]]
        selection=tk.StringVar(value=noms[0])
        comb=ttk.Combobox(panel,textvariable=selection,values=noms,state='readonly')
        comb.pack(anchor='w',pady=8)
        zone=tk.Text(panel,font=('Consolas',10),undo=True)
        zone.pack(fill='both',expand=True)
        draft=deepcopy(self.config_data['clans'])

        def afficher(nom):
            zone.delete('1.0','end')
            zone.insert('1.0',json.dumps(draft[nom],ensure_ascii=False,indent=2))

        def memoriser():
            try:
                edits=json.loads(zone.get('1.0','end'))
                # Effectuer la validation complète dans une copie temporaire.
                essais=deepcopy(self.config_data)
                essais['clans'][current[0]]=edits
                valider_configuration(essais)
                draft[current[0]]=edits
                return True
            except Exception as exc:
                messagebox.showerror('Erreur dans '+current[0],str(exc),parent=fen)
                return False

        def changer(_event):
            if memoriser():
                current[0]=selection.get()
                afficher(current[0])
            else:
                selection.set(current[0])

        comb.bind('<<ComboboxSelected>>',changer)

        def sauvegarder():
            if memoriser():
                self.config_data['clans']=draft
                fen.destroy()

        ttk.Button(panel,text='Valider les modifications des huit clans',
                   command=sauvegarder).pack(anchor='e',pady=10)
        afficher(current[0])

    def _etat_activite(self,occupe):
        """Désactiver les commandes critiques durant un calcul en arrière-plan."""
        self.active=occupe
        self.btn_sim.config(state='disabled' if occupe else 'normal')
        self.btn_exist.config(state='disabled' if occupe else 'normal')
        self._activer_pdf_si_csv()

    def _message_de_worker(self,message):
        # Les mises à jour visuelles sont programmées sur le fil Tkinter.
        self.after(0,lambda:self.statut.set(message))

    def lancer(self):
        try:
            cfg=self.lire_reglages()
        except Exception as exc:
            messagebox.showerror('Paramètres invalides',str(exc))
            return
        self._etat_activite(True)
        self.progress['value']=0
        self.statut.set('Simulation en cours : les statistiques CSV seront enregistrées à la fin.')
        parent=self.output_parent.get()
        def progression(i,n):
            self.after(0,lambda:self.progress.configure(value=100*i/max(1,n)))
            self._message_de_worker(f'Simulation : {i} / {n} parties terminées…')

        def travail():
            try:
                result=executer(cfg,parent,progression)
            except Exception as exc:
                self.after(0,lambda msg=str(exc):self._termine_sim(None,msg))
            else:
                self.after(0,lambda:self._termine_sim(result,None))
        threading.Thread(target=travail,daemon=True).start()

    def _termine_sim(self,result,erreur):
        self._etat_activite(False)
        if erreur:
            self.statut.set('Erreur de simulation : '+erreur)
            messagebox.showerror('Erreur de simulation',erreur)
            return
        self.experience.set(result['dossier'])
        self.progress['value']=100
        self._activer_pdf_si_csv()
        self.statut.set(f'CSV créés (graine : {result["graine_utilisee"]}). Cliquez sur « GÉNÉRER LE RAPPORT PDF ».')
        messagebox.showinfo('Simulation terminée',
            f"{result['parties']} parties simulées.\nLes CSV sont enregistrés dans :\n"
            f"{result['dossier']}\nGraine utilisée : {result['graine_utilisee']}\n\nCliquez sur le bouton de rapport PDF.")

    def rapport_pdf(self):
        folder=self.experience.get()
        if not (Path(folder)/'resultats_par_joueur.csv').is_file():
            messagebox.showerror('Impossible de créer le PDF','Sélectionnez un dossier contenant les CSV.')
            return
        self._etat_activite(True)
        self.progress['value']=0
        self.statut.set('Lecture des CSV pour créer le PDF…')
        def avancement(texte):
            self._message_de_worker(texte)
            self.after(0,lambda:self.progress.step(25))
        def travail():
            try:
                result=rapport_depuis_csv(folder,avancement)
            except Exception as exc:
                self.after(0,lambda msg=str(exc):self._termine_pdf(None,msg))
            else:
                self.after(0,lambda:self._termine_pdf(result,None))
        threading.Thread(target=travail,daemon=True).start()

    def _termine_pdf(self,result,erreur):
        self._etat_activite(False)
        if erreur:
            self.statut.set('Erreur pendant le PDF : '+erreur)
            messagebox.showerror('Rapport PDF',erreur)
            return
        self.progress['value']=100
        self.statut.set('Rapport PDF et graphiques enregistrés : '+result['fichier_pdf'])
        if messagebox.askyesno('Rapport terminé',
            f"Le rapport PDF est prêt !\n\n{result['fichier_pdf']}\n\nL’ouvrir maintenant ?"):
            # Windows ouvre le PDF avec le lecteur configuré par l'utilisateur.
            if sys.platform.startswith('win'):
                os.startfile(result['fichier_pdf'])
            else:
                try:
                    import subprocess
                    subprocess.Popen(['xdg-open',result['fichier_pdf']])
                except Exception:
                    pass

# ========= LANCEMENT : MODE FENÊTRE OU LIGNE DE COMMANDE =========
def main():
    """Par défaut : fenêtre ; --simuler / --rapport pour les tests automatisés."""
    parser=argparse.ArgumentParser(description='Aurorea tout-en-un : simulation et rapport PDF')
    parser.add_argument('--simuler',action='store_true',help='Simuler sans ouvrir de fenêtre')
    parser.add_argument('--rapport',metavar='DOSSIER',help='Créer le PDF à partir des CSV de ce dossier')
    parser.add_argument('--out',default=str(HOME/'Statistiques_Aurorea'),help='Dossier parent des expériences')
    parser.add_argument('--parties',type=int,help='Nombre total de parties à simuler')
    parser.add_argument('--graine',type=int,help='0 : nouvelle graine aléatoire ; autre valeur : reproductible')
    parser.add_argument('--troc',type=int,help='Points par échange accepté')
    parser.add_argument('--saisons',nargs='+',type=int,choices=[4,8],help='Scénarios de 4 et/ou 8 saisons')
    parser.add_argument('--sans-evenements',action='store_true',help='Ne jouer que sans événements')
    parser.add_argument('--config',help='Charger des paramètres JSON (facultatif)')
    parser.add_argument('--test',action='store_true',help='Contrôles internes du moteur')
    args=parser.parse_args()
    if args.test:
        test()
        print('Contrôles du moteur : OK')
        return
    if args.rapport:
        result=rapport_depuis_csv(args.rapport,lambda msg:print(msg,flush=True))
        print('PDF prêt :',result['fichier_pdf'])
        return
    if args.simuler:
        config=charger_configuration(args.config) if args.config else configuration_defaut()
        if args.parties is not None:config['simulation']['parties']=args.parties
        if args.graine is not None:config['simulation']['graine']=args.graine
        if args.troc is not None:config['simulation']['points_par_troc']=args.troc
        if args.saisons is not None:config['simulation']['saisons']=sorted(set(args.saisons))
        if args.sans_evenements:config['simulation']['avec_evenements']=[False]
        result=executer(config,args.out,lambda i,n:print(f'{i}/{n} parties',flush=True))
        print('Graine réellement utilisée :',result['graine_utilisee'])
        print('CSV prêts :',result['dossier'])
        print('Pour le PDF : python Aurorea_Tout_En_Un.py --rapport "'+result['dossier']+'"')
        return
    InterfaceAurorea().mainloop()


if __name__=='__main__':
    main()
