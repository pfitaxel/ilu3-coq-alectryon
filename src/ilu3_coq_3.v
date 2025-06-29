(*|
==============================================
ILU3 - Partie Coq - Modules et Types Abstraits
==============================================

:Auteurs: Jean-Paul Bodeveix (resp. UE), Erik Martin-Dorel, Pierre Roux
:Date:    L3 Info, Année 2023-2024

Supports de ce cours :

-  https://pfitaxel.github.io/ilu3-coq-alectryon/

Elements de correction du dernier CTD
=====================================

Lemma app_assoc :
  forall T (l1 l2 l3 : list T), l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
induction l1; simpl; intros; auto.
rewrite IHl1.
reflexivity.
Qed.

Lemma rev_app_distr :
   forall T (l1 l2 : list T), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
induction l1; simpl; intros.
apply app_nil.
rewrite IHl1.
rewrite app_assoc.
reflexivity.
Qed.

Exercices bonus
--------------

- Définir la version récursive terminale de `rev`, et prouver en Coq
  que les deux versions sont équivalentes.

- Définir les versions directe et récursive terminale de `fact` et prouver en Coq leur équivalence.

- Définir les versions directe et récursive terminale de `pow n f` calculant n compositions de f et prouver en Coq leur équivalence.


Modules en Coq et application aux TAD
=====================================

1. Spécification de modules (types de modules)
----------------------------------------------

Déclaration d’identificateurs.

On distingue :

-  des identificateurs de types

-  des identificateurs de constantes ou d’opérations

-  des identificateurs de propriétés (axiomes)

Exemple

.. coq::
|*)
Module Type Monoide.
  Parameter T : Type.           (* une sorte *)
  Parameter un : T.             (* une constante *)
  Parameter prod : T -> T -> T. (* une opération *)

  Axiom assoc :
    forall x y z : T, prod x (prod y z) = prod (prod x y) z.
  Axiom neutre_g : forall x, prod un x = x.
  Axiom neutre_d : forall x, prod x un = x.
End Monoide.
(*|

2. Modules réalisant une spécification
--------------------------------------

Définition des identificateurs déclarés dans la spécification

Implantations possibles du monoide :

-  listes avec concaténation

-  entiers avec :math:`0` et :math:`+`

-  entiers avec :math:`1` et :math:`*`

-  type singleton

-  …

Exemple : monoide des listes avec concaténation
-----------------------------------------------

.. coq::
|*)
Require Import List. Import ListNotations.
Set Implicit Arguments.

Module MonoList <: Monoide. (* vérification sans masquage *)
  Definition T := list nat.
  Definition un : T := [].
  Definition prod (x y : T) := x ++ y.

  Lemma assoc :
    forall x y z : T, prod x (prod y z) = prod (prod x y) z.
  Proof. apply app_assoc. Qed.

  Lemma neutre_g : forall x, prod un x = x.
  Proof. reflexivity. Qed.

  Lemma neutre_d : forall x, prod x un = x.
  Proof. induction x; auto. simpl. rewrite IHx. reflexivity. Qed.
End MonoList.
(*|

**Exercice :** définir un module `MonoAdd` implémentant
la signature de Monoide pour les entiers munis de l'addition,
et un module `MonoMul` implémentant cette même signature pour les entiers
munis de la multiplication.

3. Utilisation indépendante de l’implantation (foncteur)
--------------------------------------------------------

Exemple : unicité de l’élément neutre

.. coq::
|*)
Module Use(M : Monoide).
  Theorem unicite :
    forall u : M.T, (forall x, M.prod x u = x) -> u = M.un.
  Proof.
  intros u Hu.
  rewrite <-(Hu M.un).
  rewrite M.neutre_g.
  reflexivity.
  Qed.
End Use.
(*|

4. Instantiation du foncteur (a.k.a. module paramétré)
------------------------------------------------------

Exemple

.. coq::
|*)
Module Inst := Use(MonoList).
  Check Inst.unicite.  (* .unfold *)

  Print MonoList.un.  (* .unfold *)
  Print MonoList.T.  (* .unfold *)
(*|

Exemple autour de la structure de pile
======================================

Signature d’un TAD Pile
-----------------------

Ecrire la spécification du type abstrait tPile introduisant un type
Elem, un type P, et les opérations habituelles sur les piles. On
essaiera d’étendre au maximum le domaine des fonctions partielles (par
ex. en retournant la pile vide), ou si besoin en utilisant le type
option :

.. coq::
|*)
Inductive option {T : Type} := None | Some (valeur : T).

Module Type Pile.
  Parameter Elem : Type.
  Parameter P : Type.
  Parameter vide : P.
  Parameter push : Elem -> P -> P.
  Parameter estVide : P -> bool.
  Parameter top : P -> @option Elem.
  Parameter pop : P -> P.
  (* et pas "P -> option P" :
   * choix de conception pour simplifier les preuves *)

  Axiom estVide_vide : estVide vide = true.
  Axiom estVide_push : forall p e, estVide (push e p) = false.
  Axiom top_vide : top vide = None.
  Axiom top_push : forall p e, top (push e p) = Some e.
  Axiom pop_vide : pop vide = vide.
  Axiom pop_push : forall p e, pop (push e p) = p.
End Pile.
(*|

Implémentation du TAD Pile
--------------------------

Implémentez un TAD Pile d’entiers naturels,
en vous appuyant sur la bibliothèque des listes.

.. coq::
|*)
Module Pile_Liste <: Pile.
  Definition Elem := nat.
  Definition P := list nat.
  Definition vide : P := [].
  Definition push (e : Elem) (p : P) := e :: p.
  Definition estVide (p : P) :=
    match p with [] => true | _ => false end.
  Definition top (p : P) :=
    match p with [] => None | x :: _ => Some x end.
  Definition pop (p : P) :=
    match p with [] => [] | _ :: l => l end.

  Lemma estVide_vide : estVide vide = true.
  Proof. reflexivity. Qed.

  Lemma estVide_push : forall p e, estVide (push e p) = false.
  Proof. intros p e. reflexivity. Qed.

  Lemma top_vide : top vide = None.
  Proof. reflexivity. Qed.

  Lemma top_push : forall p e, top (push e p) = Some e.
  Proof. intros p e. reflexivity. Qed.

  Lemma pop_vide : pop vide = vide.
  Proof. reflexivity. Qed.

  Lemma pop_push : forall p e, pop (push e p) = p.
  Proof. intros p e. reflexivity. Qed.
End Pile_Liste.
(*|

Autre exemple d’implémentation
------------------------------

Peut-on implémenter le même TAD avec des
listes, mais en empilant et dépilant en queue ?

.. coq::
|*)
Module Pile_QListe <: Pile.
  Definition Elem := nat.
  Definition P := list nat.
  Definition vide : P := [].
  Definition push (e : Elem) (p : P) := p ++ [e].
  Definition estVide (p : P) :=
    match p with [] => true | _ => false end.
  Fixpoint top (p : P) :=
    match p with [] => None | [e] => Some e | x:: l => top l end.
  Fixpoint pop (p : P) :=
    match p with [] => [] | [e] => [] | x :: l => x :: pop l end.

  Lemma estVide_vide : estVide vide = true.
  Proof. reflexivity. Qed.

  Lemma estVide_push : forall p e, estVide (push e p) = false.
  Proof. induction p; simpl; auto. Qed.

  Lemma top_vide : top vide = None.
  Proof. reflexivity. Qed.

  Lemma top_push : forall p e, top (push e p) = Some e.
  Proof. induction p; auto; destruct p; auto. Qed.

  Lemma pop_vide : pop vide = vide.
  Proof. reflexivity. Qed.

  Lemma pop_push : forall p e, pop (push e p) = p.
  Proof.
  induction p; auto.
  destruct p; auto.
  intros e; rewrite <-(IHp e) at 2; auto.
  Qed.
End Pile_QListe.
(*|

Pour aller plus loin
--------------------

Pour rappel, il est important d'avoir terminé chaque TP avant d'aborder le suivant.

Si vous voulez réviser ou approfondir les notions vues en CTD et TP Coq,
ou faire d'autres exercices pour vous entraîner,
voici 3 ressources supplémentaires, classées par ordre croissant de longueur :

- `<https://rocq-prover.org/docs/tour-of-rocq>`_
- `<https://learnxinyminutes.com/coq/>`_
- `<https://cel.hal.science/inria-00001173>`_ (Coq in a Hurry, avec des exercices)
|*)
