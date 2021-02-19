(*|
=================================
Aperçu des fonctionnalités de Coq
=================================

:Auteurs: Jean-Paul Bodeveix (resp. UE), Erik Martin-Dorel, Pierre Roux
:Date:    L3 Info, Semestre 6, Année 2020-2021

Aperçu des fonctionnalités de Coq
=================================

Présentation du logiciel Coq
----------------------------

-  Implémenté en OCaml

.. image:: https://coq.inria.fr/files/barron_logo.png
   :alt: Coq
   :target: https://coq.inria.fr

-  Initié par Thierry Coquand et Gérard Huet, et développé par Inria
   depuis 1984 (la dernière version stable étant, lors de l'écriture de
   ce document, Coq 8.13).

.. image:: https://img.shields.io/docker/v/coqorg/coq/latest
   :alt: coq latest version
   :target: https://github.com/coq/coq/releases
|*)

(*|
-  Comprend un langage fonctionnel pur, statiquement typé, et
   *très expressif* (on détaillera cet aspect dans quelques minutes),
   muni d’un environnement de preuve interactive (vu au Cours n°2).

-  Coq a une grande communauté d’utilisateurs. Projets notables :

   -  CompCert : compilateur C99 complètement prouvé en Coq [Inria]

   -  C-CoRN : bibliothèque d’analyse constructive [à Nijmegen]

   -  Preuve formelle du théorème des 4 couleurs [G. Gonthier,
      B. Werner]

   -  MathComp : bibliothèque d’algèbre et preuve formelle du théorème
      de Feit–Thompson (la preuve papier fait :math:`{>}300` pages)
      [Inria, Microsoft Research]

   -  | Vérification de systèmes critiques (voir par exemple :
      | `<https://github.com/ligurio/practical-fm>`_)

-  Ouvrage (publié chez Springer et téléchargeable en français) :

   `Coq'Art: Interactive Theorem Proving and Program Development
   <http://www.labri.fr/perso/casteran/CoqArt/coqartF.pdf>`_

TODO Fiat-Crypto

|*)

(*|
Caractéristiques intéressantes de Coq
-------------------------------------

-  langage fonctionnel pur proche d’OCaml

   -  terminaison garantie (impossible d’écrire ``let rec f x = f x``)

   -  typage fort et très expressif (on peut définir des listes à taille
      fixée, des fonctions à arité variable, etc.)

-  | langage logique (expression de formules quantifiées, etc.)
   | `forall n : nat, n > 0 -> exists m : nat, S m = n`

-  environnement de preuve (assistance à la construction de preuve)

-  | vérification automatique de la correction de ces preuves
   | vérification de preuve = vérification de type

-  | tactiques utilisateur pour automatiser les preuves :
   | `tauto` pour la logique des propositions,
   | `firstorder` pour la logique du premier ordre,
   | `lia` pour l’arithmétique linéaire sur les entiers
     (`2 * (n + 1) - n > n`)
   | etc.
|*)

Require Import Lia. (* pour utiliser la tactique "lia" *)

(*|
Rappel : installation de l’environnement de TP
----------------------------------------------

Environnement recommandé
~~~~~~~~~~~~~~~~~~~~~~~~

-  Coq 8.12 + Emacs + ProofGeneral + Company-Coq [cf. tutoriel ci-dessous]

-  Carte de référence / raccourcis clavier [cf. Moodle]

-  Dictionnaire OCaml/Coq [cf. Moodle]

Tutoriel d’installation
~~~~~~~~~~~~~~~~~~~~~~~

- avec OPAM, sous GNU/Linux, macOS ou Windows 10 :

  `<https://github.com/erikmd/tapfa-init.el>`_

-  *n’hésitez pas à poser des questions sur Moodle/Discord ;
   on vous demandera un feedback au dernier TP.*
|*)

(*|
Utilisations possibles de Coq
-----------------------------

-  Synthèse du type d’une expression :
|*)

Check fun x y => x + y + 1.
(* .unfold *)

(*|
-  Évaluation d’expressions (calcul) :
|*)

Eval compute in (fun x y => x+y+1) 2 3.
(* .unfold *)

(*|
-  Implantation de fonctions et vérification de leurs propriétés :
|*)

Definition f x := x + 2.

Theorem f_croissante : forall x y : nat, x < y -> f x < f y.
Proof.
(* On ne détaille pas pour le moment le script de preuve => Cours 2 *)
intros x y; unfold f; lia. (* .none *)
Qed.

(*|
- Définition de sous-types :
|*)

Definition Mod3 := {x : nat | x < 3}.

(*|
-  Synthèse de fonctions à partir d’une preuve de sa spécification :
|*)

(* TODO Replace with list example *)

Definition pred :
  forall n : nat, (* précond *) n > 0 ->
    {m : nat | (* postcond *) S m = n}.
Proof.
(* On ne détaille pas pour le moment le script de preuve *)
destruct n as [|n'];
  [ lia
  | intros _; exists n'; reflexivity]. (* .none *)
Defined.

Require Extraction.
(* Génération automatique de code OCaml à partir du code Coq prouvé *)
Recursive Extraction pred. (* .unfold *)

(*|
Motivations pour utiliser Coq
=============================

Positionnement de Coq par rapport aux types abstraits
-----------------------------------------------------

Par rapport à PFITA
~~~~~~~~~~~~~~~~~~~

-  **explicitation des axiomes** dans la spécification des types abstraits

-  **preuve formelle** que l'implémentation satisfait bien la spécification

-  compilation et **vérification** modulaire possible

   (implémentation et **vérification** d'un composant utilisateur
   indépendemment de l'implémentation du composant utilisé)

-  donc : plus besoin de tests unitaires ou d'intégration...

-  mais : Toujours besoin de **validation** de l'implémentation par
   rapport aux exigences attendues (qui peuvent différer des exigences
   exprimées dans le cahier des charges !)

   Voir aussi : la notion de `V & V <https://en.wikipedia.org/wiki/V%20&%20V>`_
|*)

(*|
Exemple de vérification modulaire
---------------------------------

-  Définition d'une signature
|*)

Module Type tPickGt.
  Parameter pick : nat -> nat.
  Axiom pick_gt : forall n, pick n > n.
End tPickGt.

(*|
-  Implantation de la signature
|*)

Module PickGt <: tPickGt. (* vérif conformité sans masquage *)
  Definition pick n := S n.
  Lemma pick_gt : forall n, pick n > n.
  Proof. auto. Qed.
End PickGt.

(*|
-  Utilisation d'un module respectant la signature
|*)

Module Use (P : tPickGt).
  Definition num := P.pick O.
  Lemma num_gt0 : num > O.
  Proof. apply P.pick_gt. Qed.
End Use.

(*|
-  Instantiation du module paramétré
|*)

Module M := Use(PickGt).

(*|
Introduction à Coq
==================

Types et expressions
--------------------

| À retenir En Coq, tout terme bien formé a un type (y compris les types !)
| donc contrairement à OCaml, les termes/expressions et les types ne
  forment pas deux "collections disjointes"

Exemples d’expressions Coq et leur type
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

+------------------+-------------+--------------+-------------+
| valeur/programme | type        | type de type | …           |
+==================+=============+==============+=============+
| 0                | nat         | Set          | …           |
+------------------+-------------+--------------+-------------+
| true             | bool        | Set          | …           |
+------------------+-------------+--------------+-------------+
| fun x => x + 1   | nat -> nat  | Set          | …           |
+------------------+-------------+--------------+-------------+

Exemples en Coq
---------------
|*)

(* TODO unfold *)

Check 0. (* 0 : nat *)
Check true. (* true : bool *)
Check fun x => x + 1. (* fun x => x + 1 : nat -> nat *)
Check nat. (* nat : Set *)
Check Set. (* Set : Type *)

(*|
Exemples avancés d’expressions Coq et leur type.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Remarque :

-  `Prop` est le type des formules logiques ;

-  à ne pas confondre avec `bool`, le type des booléens.

Les deux ont leur utilité :

-  les prédicats renvoyant un `bool` correspondent à des "prédicats calculables"
   (par exemple un algorithme décidant si un entier est pair ou pas) :
   on peut déterminer leur résultat par un *calcul* ;

-  les prédicats renvoyant un `Prop` correspondent à des "prédicats logiques"
   (définis par une formule) :
   on peut prouver leur véracité par un *raisonnement*.

+-------------------+----------------+--------------+-------------+
| valeur/programme  | type           | type de type | …           |
+===================+================+==============+=============+
| list              | Type -> Type   | Type         | …           |
+-------------------+----------------+--------------+-------------+
| "preuve de `1<2`" | 1 < 2          | Prop         | …           |
+-------------------+----------------+--------------+-------------+
| "(1,              | {x: nat | x>0} | Set          | …           |
| preuve de `1>0`)" |                |              |             |
+-------------------+----------------+--------------+-------------+
|*)
