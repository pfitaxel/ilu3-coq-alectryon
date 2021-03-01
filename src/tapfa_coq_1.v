(*|
=================================
Aperçu des fonctionnalités de Coq
=================================

:Auteurs: Jean-Paul Bodeveix (resp. UE), Erik Martin-Dorel, Pierre Roux
:Date:    L3 Info, Semestre 6, Année 2020-2021

Supports de ce cours :

-  https://pfitaxel.github.io/tapfa-coq-alectryon/

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

   -  `FiatCrypto <https://github.com/mit-plv/fiat-crypto>`_ :
      "Simple High-Level Code For Cryptographic Arithmetic: With
      Proofs, Without Compromises" (*Implementations from our library
      were included in BoringSSL to replace existing specialized code,
      for inclusion in several large deployments for Chrome, Android,
      and CloudFlare.*)

-  Ouvrage (publié chez Springer et téléchargeable en français) :

   `Coq'Art: Interactive Theorem Proving and Program Development
   <http://www.labri.fr/perso/casteran/CoqArt/coqartF.pdf>`_
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

-  Coq 8.12 + Emacs + ProofGeneral + Company-Coq
   [cf. `tutoriel <https://github.com/erikmd/tapfa-init.el>`_]

-  Carte de référence / raccourcis clavier [cf. Moodle]

-  Dictionnaire OCaml/Coq [cf. Moodle ; autorisé à l'examen a priori]

Tutoriel d’installation
~~~~~~~~~~~~~~~~~~~~~~~

- avec OPAM, sous GNU/Linux, macOS ou Windows 10 :

  `<https://github.com/erikmd/tapfa-init.el>`_

-  à installer avant le 1er TP TAPFA-Coq

-  n’hésitez pas à poser des questions sur Moodle/Discord
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

| À retenir :
| En Coq, tout terme bien formé a un type (y compris les types !)
| donc contrairement à OCaml, les termes/expressions et les types ne
  forment pas deux "collections disjointes"

Exemples d’expressions Coq et leur type
---------------------------------------

+------------------+--------------+--------------+-------------+
| valeur/programme | type         | type de type | …           |
+==================+==============+==============+=============+
| `0`              | `nat`        | Set          | …           |
+------------------+--------------+--------------+-------------+
| `true`           | `bool`       | Set          | …           |
+------------------+--------------+--------------+-------------+
| `fun x => x + 1` | `nat -> nat` | Set          | …           |
+------------------+--------------+--------------+-------------+
|*)

Check 0.
(* .unfold *)
Check true.
(* .unfold *)
Check fun x => x + 1.
(* .unfold *)
Check nat.
(* .unfold *)
Check Set.
(* .unfold *)

(*|
Exemples avancés d’expressions Coq et leur type
-----------------------------------------------

+--------------------+------------------+--------------+-------------+
| valeur/programme   | type             | type de type | …           |
+====================+==================+==============+=============+
| `list`             | `Type -> Type`   | `Type`       | …           |
+--------------------+------------------+--------------+-------------+
| "preuve de `2<=2`" | `2 <= 2`         | `Prop`       | …           |
+--------------------+------------------+--------------+-------------+
| "(1;               | `{x: nat | x>0}` | `Set`        | …           |
|  preuve de `1>0`)" |                  |              |             |
+--------------------+------------------+--------------+-------------+
|*)

Check 2 <= 2.
(* .unfold *)
Check le 2 2.
(* .unfold *)
Check le_n 2.
(* .unfold *)
Check le_n.
(* .unfold *)
Check le.
(* .unfold *)
(* Prop est le type des formules logiques *)
Check Prop.
(* .unfold *)

(*|
Remarques
---------

-  `Prop` est le type des formules logiques ;

-  à ne pas confondre avec `bool`, le type des booléens.

Les deux ont leur utilité :

-  les prédicats renvoyant un `bool` correspondent à des "prédicats calculables"
   (par exemple un algorithme décidant si un entier est pair ou pas) :
   on peut déterminer leur résultat par un *calcul* ;

-  les prédicats renvoyant un `Prop` correspondent à des "prédicats logiques"
   (définis par une formule) :
   on peut prouver leur véracité par un *raisonnement*.
|*)

(*|
Le type des listes : comparaison OCaml / Coq
--------------------------------------------

+-----------------------------+------------------------------------------+
| OCaml                       | Coq                                      |
+=============================+==========================================+
| `'a list`                   | `list a`                                 |
+-----------------------------+------------------------------------------+
| `bool list`                 | `list bool`                              |
+-----------------------------+------------------------------------------+
| notation spéciale postfixée | `list` est une fonction : `Type -> Type` |
+-----------------------------+------------------------------------------+
|*)

Check list.
(* .unfold *)

(*|
Éléments de syntaxe
-------------------

-  Les mots "terme" et "expression" sont synonymes.

- | Rappel :
  | En Coq, tout terme bien formé a un type (y compris les types !) ;
  | contrairement à OCaml, les termes/expressions et les types ne
    forment pas deux "collections disjointes" ;
  | donc la grammaire des termes ci-dessous contient aussi Type, Set, Prop :

.. code-block:: Coq

   terme ::= Type | Set | Prop           "sortes" (= types de type)
           | var                         "variable"
           | ( terme )
           | terme terme                 "application"
           | terme op terme              "opérateur infixe"
           | fun var : terme ⇒ terme     "abstraction"
           | let var := terme in terme   "définition locale"
           | if terme then terme else terme
           | terme -> terme              "type flèche" (= type des fonctions)

|*)

(*|
Exemples
--------
|*)

Check fun x => x + 1.

Check (fun f x => f (f x)) (fun x => x + 1).

Eval compute in (fun f x => f (f x)) (fun x => x + 1) 3.

Definition f1 := fun x => x + 1. Eval compute in f 0.

Definition double f := fun (x : nat) => f (f x). Check double.

Definition double2 (f : nat -> nat) := fun x => f (f x). Check double2.

Fail Definition double3 f := fun x => f (f x).

(*|
Cette dernière définition est refusée car en Coq, les *paramètres de
généricité* sont explicites. Pas de synthèse automatique de leur nom ;
il faut expliciter ces arguments.
|*)

(*|
Généricité
----------

Une fonction générique prend un type en paramètre.

Exemple de définition d'une fonction générique : la fonction identité.
|*)

Definition id := fun (T:Type) => fun (x:T) => x.
(* ou *)
Definition id_v2 := fun (T:Type) (x:T) => x.
(* ou *)
Definition id_v3 (T:Type) := fun (x:T) => x.
(* ou *)
Definition id_v4 (T:Type) (x:T) := x.
(* ou *)
Definition id_v5 T (x:T) := x.

(*| :math:`\leadsto` ces fonctions ont toutes 2 arguments ! *)

(*|
Utilisation d’une fonction générique
|*)

Check id nat.
(* .unfold *)
Check id nat 0.
(* .unfold *)
Check id bool.
(* .unfold *)
Check id bool true.
(* .unfold *)

Print id.
(* .unfold *)

(*|
Généricité et typage
--------------------

Type d’une fonction générique

-  En OCaml: ``id: 'a -> 'a`` :math:`\leadsto` pour tout type ``'a``,
   id prend un argument de type ``'a`` et retourne un résultat de
   type ``'a``

-  En Coq: `id: forall a, a -> a` :math:`\leadsto` la quantification
   est explicite

-  extension du langage des termes :

.. code-block:: Coq

   terme ::= Type | Set | Prop
           | var
           | ( terme )
           | terme terme
           | terme op terme
           | fun var : terme ⇒ terme
           | let var := terme in terme
           | if terme then terme else terme
           | terme -> terme             (type d'une fonction)
           | forall var : terme, terme  (type d'une fonction générique)

- | Comme on le verra par la suite, `t1 -> t2` est en fait
  | une syntaxe alternative (plus intuitive) pour "`forall _ : t1, t2`".
|*)

Check id.
(* .unfold *)

(*|
Généricité et arguments implicites I
------------------------------------

Les remarques qui suivent ne sont pas "exigibles à l'examen" mais
permettront d'avoir plus de confort, notamment en TP, en évitant de
devoir expliciter tous les paramètres de généricité lors de l'appel
d'une fonction polymorphe.

Redéfinissons la fonction id après activation des arguments implicites
|*)

Set Implicit Arguments. (* au début du fichier en principe *)

Definition id' (T:Type) (x:T) := x.
Print id'.
(* .unfold *)

(* même code que *)
Print id.
(* .unfold *)

(* mais *)
About id'.
(* id' : forall [T : Type], T -> T *)

(*|
l'argument T est implicite : il peut être inféré à partir de l'argument d'après.

D'où une syntaxe concise à la OCaml :
|*)

Check id' 0.
(* .unfold *)

Set Printing All. (* affiche tout, dont les arguments implicites *)
Check id' 0.
(* .unfold *)

Unset Printing All.

(*|
Généricité et arguments implicites II
-------------------------------------

En OCaml :

``let id x = x;;``

``id 0;; (* : int = 0 *)``

``id true;; (* : bool = true *)``

En Coq :

`Set Implicit Arguments.`

`Definition id T (x:T) := x.`

`Check id 0. (* id 0 : nat *)`

`Check id true. (* id true : bool *)`
|*)

(*|
Paramètres de généricité : un plus gros exemple
-----------------------------------------------

En OCaml :

``let comp f g x = g (f x);;``

``val comp : (’a -> ’b) -> (’b -> ’c) -> ’a -> ’c = <fun>``

``comp (fun x -> x + 1) (fun x -> x * 2) 3;;``

:math:`\leadsto` ?

En Coq :

Pas de synthèse du nom des paramètres de généricité : il faut
déclarer ces paramètres de généricité lors de la définition.
|*)

(* Set Implicit Arguments. (* déjà fait auparavant *) *)

Definition comp T1 T2 T3 (f:T1->T2) (g:T2->T3) (x:T1): T3 := g (f x).
(* ou *)
Definition comp_v2 T1 T2 T3 (f:T1->T2) (g:T2->T3) (x:T1) := g (f x).
(* ou *)
Definition comp_v3 T1 T2 T3 (f:T1->T2) (g:T2->T3) x := g (f x).
(* ou *)
Definition comp_v4 T1 T2 T3 f (g:T2->T3) (x:T1) := g (f x).
(* ou *)
Definition comp_v5 T1 T2 T3 (f:T1->T2) g (x:T1) : T3 := g (f x).

Eval compute in comp (fun x => x + 1) (fun x => x * 2) 3.
