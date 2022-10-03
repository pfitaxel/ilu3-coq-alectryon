(*|
==================
TAPFA - Partie Coq
==================

:Auteurs: Jean-Paul Bodeveix (resp. UE), Erik Martin-Dorel, Pierre Roux
:Date:    L3 Info, Semestre 6, Année 2021-2022

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
   ce document, Coq 8.15.0).

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

-  Coq 8.15 + Emacs + ProofGeneral + Company-Coq
   [cf. `tutoriel <https://github.com/erikmd/tapfa-init.el>`_]

-  Carte de référence / raccourcis clavier [cf. Moodle]

-  Dictionnaire OCaml/Coq [cf. Moodle ; autorisé à l'examen a priori]

Tutoriel d’installation
~~~~~~~~~~~~~~~~~~~~~~~

- avec OPAM, sous GNU/Linux, macOS ou Windows 10 :

  `<https://github.com/erikmd/tapfa-init.el>`_

-  à installer avant le 1er TP TAPFA-Coq

-  avant cela, jsCoq peut être utilisé dans votre navigateur :

  `<https://jscoq.github.io/scratchpad.html>`_

-  n’hésitez pas à poser des questions sur Moodle
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

+------------------------+------------------+--------------+-------------+
| valeur/programme       | type             | type de type | …           |
+========================+==================+==============+=============+
| `list`                 | `Type -> Type`   | `Type`       | …           |
+------------------------+------------------+--------------+-------------+
| "preuve de `2<=2`"     | `2 <= 2`         | `Prop`       | …           |
+------------------------+------------------+--------------+-------------+
| "(1; preuve de `1>0`)" | `{x: nat | x>0}` | `Set`        | …           |
+------------------------+------------------+--------------+-------------+
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

+-----------------------------------+------------------------------------------+
| OCaml                             | Coq                                      |
+===================================+==========================================+
| `'a list`                         | `list a`                                 |
+-----------------------------------+------------------------------------------+
| `bool list`                       | `list bool`                              |
+-----------------------------------+------------------------------------------+
| notation spéciale, mais familière | `list` est une fonction : `Type -> Type` |
+-----------------------------------+------------------------------------------+
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

Que renvoient les commandes suivantes ?
|*)

Check fun x => x + 1.

Check (fun f x => f (f x)) (fun x => x + 1).

Eval compute in (fun f x => f (f x)) (fun x => x + 1) 3.

Definition f1 := fun x => x + 1. Eval compute in f1 0.

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

Definition id := fun (T : Type) => fun (x : T) => x.
(* ou *)
Definition id_v2 := fun (T : Type) (x : T) => x.
(* ou *)
Definition id_v3 (T : Type) := fun (x : T) => x.
(* ou *)
Definition id_v4 (T : Type) (x : T) := x.
(* ou *)
Definition id_v5 T (x : T) := x.

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

-  En OCaml : ``id : 'a -> 'a`` :math:`\leadsto` pour tout type ``'a``,
   id prend un argument de type ``'a`` et retourne un résultat de
   type ``'a``

-  En Coq : `id : forall a, a -> a` :math:`\leadsto` la quantification
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
  | une syntaxe alternative (plus intuitive) de "`forall _ : t1, t2`".
|*)

Check id.
(* .unfold *)

(*|
Inférence d'arguments
---------------------

Dans le terme `id bool true` ci dessus, Coq pourrait deviner
automatiquement le premier argument `bool` puisque c'est le type
du deuxième argument `true` d'après le type de `id`. Il est
effectivement possible d'écrire
|*)
Check id _ true.
(* .unfold *)
(*|
Coq remplace automatiquement le `_` par la seule valeur possible `bool`.

On peut ainsi remplacer tout sous terme par un trou `_` et laisser Coq
tenter de le remplir. Coq retourne une erreur quand il ne trouve pas
de solution canonique.
|*)
Fail Definition id_bool := id bool _.

(*|
Généricité et arguments implicites I
------------------------------------

Les remarques qui suivent ne sont pas "exigibles à l'examen" mais
permettront d'avoir plus de confort, notamment en TP, en évitant de
devoir expliciter tous les paramètres de généricité lors de l'appel
d'une fonction polymorphe.

Les arguments implicites permettent d'écrire `id true` au lieu de `id _ true`.
Redéfinissons la fonction id après activation des arguments implicites
|*)

Set Implicit Arguments. (* au début du fichier en principe *)

Definition id' (T : Type) (x : T) := x.
Print id'.
(* .unfold *)

(* même code que *)
Print id.
(* .unfold *)

(* mais *)
About id'.
(* id' : forall [T : Type], T -> T *)
(*|
(:math:`\leadsto` noter le [T] au lieu de T)

L'argument T est implicite : il peut être inféré à partir de l'argument d'après.

D'où une syntaxe concise à la OCaml :
|*)

Check id' true.
(* .unfold *)

Set Printing All. (* affiche tout, dont les arguments implicites *)
Check id' true.
(* .unfold *)
(*|
Le `@` indique que tous les arguments de `id'` sont explicités.
Grâce aux arguments implicites, entrer `id' true` est equivalent à entrer
|*)
Check @id' _ true.
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

Definition comp T1 T2 T3 (f:T1->T2) (g:T2->T3) (x : T1) : T3 := g (f x).
(* ou *)
Definition comp_v2 T1 T2 T3 (f:T1->T2) (g:T2->T3) (x : T1) := g (f x).
(* ou *)
Definition comp_v3 T1 T2 T3 (f:T1->T2) (g:T2->T3) x := g (f x).
(* ou *)
Definition comp_v4 T1 T2 T3 f (g:T2->T3) (x:T1) := g (f x).
(* ou *)
Definition comp_v5 T1 T2 T3 (f:T1->T2) g (x:T1) : T3 := g (f x).

Eval compute in comp (fun x => x + 1) (fun x => x * 2) 3.

(*|
Exercices
---------

1. Ecrire la fonction ``mult2`` retournant le double de son argument.
|*)

Definition mult2 := (* todo *)0.

(*|
2. | **Supposons défini** le prédicat `leq : nat -> nat -> bool`,
     retournant `true` si son 1er argument est inférieur à son second.
   | Définir la fonction ``max`` retournant le plus grand de ses 2 arguments.
   | En déduire la fonction ``max3`` retournant le plus grand de ses 3 arguments.
   | Ecrire une variante ``max3'`` où la définition de ``max`` est locale.
|*)

Parameter leq : nat -> nat -> bool.

Definition max := (* todo *)0.

Definition max3 := (* todo *)0.

Definition max3' := (* todo *)0.

(*|
3. Quel est le type de l'expression suivante ?
|*)

Definition expr3 := fun (T:Type) (f:T -> T) x => f (f x).
(* *)

(*|
4. Quel est le type de l'expression suivante ? (donner 2 syntaxes équivalentes)
|*)

Definition expr4 := fun (T:Type) => T -> T.

(*|
5. Quel est le type de l'expression suivante ?
|*)

Definition expr5 := fun (T:Type) (x:T) => x=x.

(*|
6. Écrire une fonction de type `forall a b : Type, a -> b -> a`
|*)

Definition expr6 := (* todo *)0.

(*|
7. Écrire une fonction de type `forall a b : Type, a -> (a -> b) -> b`
|*)

Definition expr7 := (* todo *)0.

(*|
8. Écrire une fonction de type
`forall a b c : Type, (a -> b -> c) -> (a -> b) -> a -> c`
|*)

Definition expr8 := (* todo *)0.

(*|
9. Écrire une fonction de type `forall a b c : Type, (a -> c) -> (a -> b -> c)`
|*)

Definition expr9 := (* todo *)0.

(*|
10. Écrire une fonction de type
`forall a b c : Type, (a -> b -> c) -> b -> a -> c`
|*)

Definition expr10 := (* todo *)0.

(*|
11. Écrire une fonction de type `forall a b : Type, (a -> a -> b) -> a -> b`
|*)

Definition expr11 := (* todo *)0.

(*|
12. Peut-on écrire une fonction de type `forall a b : Type, a -> b` ?
|*)

(* En OCaml :

   let exemple =

 *)

(* En Coq ? *)

(*|
Retour sur `->` et `forall`
---------------------------

`T1 -> T2` correspond :

-  au type des fonctions de `T1` dans `T2`, c’est-à-dire

-  au type des fonctions qui associent à tout `x:T1` un élément de `T2`,

-  que l’on peut aussi écrire `forall (x : T1), T2`

`forall` est une notation :

-  généralisant `->`,

-  utile lorsque le type d’arrivée `T2` dépend du terme fourni `x`.

Exemples de types définissables en Coq
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-  `forall (T : Type), T -> T`

-  `forall (p q : nat), q <> 0 -> nat`

-  `forall (b : bool), if b then nat else bool * bool`
|*)

(*|
La correspondance de Curry–Howard : double lecture
--------------------------------------------------

+---------------+------------------------------------+------------------------+
| Notation      | Lecture fonctionnelle              | Lecture logique        |
+===============+====================================+========================+
| `x : T`       | `x` a pour type `T`                | `x` "preuve" de `T`    |
+---------------+------------------------------------+------------------------+
| *aucun* `x:T` | le type `T` est vide               | `T` est insatisfiable  |
+---------------+------------------------------------+------------------------+
| `P -> Q`      | type des fonctions de `P` dans `Q` | l'implication logique  |
+---------------+------------------------------------+------------------------+
| `f : P -> Q`  | f est une fonction de `P` dans `Q` | f preuve de ``P => Q`` |
+---------------+------------------------------------+------------------------+
|               | f transforme une "preuve" de `P` en une "preuve" de `Q`     |
+---------------+-------------------------------------------------------------+
|*)

(*|
Types inductifs
---------------

Définition d’un type inductif paramétré par ``a1,...,am``.

En OCaml :

.. code-block:: OCaml

   type ('a1, ..., 'am) t =     (* m paramètres de généricité *)
     | C1 of t1_1 * ... * t1_n1 (* constructeur C1 d'arité n1 *)
     | ...
     | Ck of tk_1 * ... * tk_nk (* kième constructeur *)

En Coq :

.. code-block:: Coq

   Inductive t a1 ... am :=
     | C1 (p1 : t1_1) ... (pn1 : t1_n1)
     | ...
     | Ck (p1 : tk_1) ... (pnk : tk_nk). (* ne pas oublier le point *)
|*)

(*|
Analyse par cas
---------------

En OCaml :

.. code-block:: OCaml

   match x with
   | C1 (x1, ..., xn1) -> ...
   | ...
   | Ck (x1, ..., xnk) -> ...

En Coq :

.. code-block:: Coq

   match x with
   | C1 x1 ... xn1 => ...
   | ...
   | Ck x1 ... xnk => ...
   end

Différences :

-  Les constructeurs sont typiquement "curryfiés" en Coq.

-  Les `->` sont remplacées par `=>`

-  Il y a un `end` en plus (pratique)

-  Sinon c'est la même syntaxe :-)
|*)

(*|
Exemples de types inductifs
---------------------------

Type de données prédéfini dans Coq :
|*)
Print bool.
(* .unfold *)

Inductive entier_nat := Zero | Succ (p : entier_nat).
Inductive liste T := Vide | Cons (x : T) (l : liste T).

(*|
Eléments d’un type inductif :
|*)

Check true.
(* .unfold *)

Check (Succ (Succ Zero)).
(* .unfold *)

Definition liste1 := @Cons entier_nat (Succ Zero) (Vide entier_nat).
Print liste1.
(* .unfold *)

(*|
Fonctions récursives
--------------------

| **Obligation de terminaison :**
| un des arguments doit être *structurellement décroissant*
| (appels récursifs sur un sous-terme de cet argument)

| Comme déjà dit en introduction :
| il est impossible de définir en Coq une fonction récursive qui ne termine pas.
|*)

Fixpoint add n m :=
  match n with
  | Zero => m
  | Succ p => Succ (add p m)
  end.

Fixpoint long T (l : liste T) :=
  match l with
  | Vide _ => Zero
  | Cons x r => Succ (long r)
  end.

(*| 
Est-ce normal d'écrire `Cons x r => Succ (long r)` ?

Précisons :

- Le constructeur `Cons` a trois arguments,

- La fonction `long` a 2 arguments...

- Mais on avait activé les arguments implicites : `Set Implicit Arguments`.

- On pourrait néanmoins écrire en étant pleinement explicite :
|*)

Fixpoint long_v2 T (l : liste T) :=
  match l with
  | Vide _ => Zero
  | @Cons _ x r => Succ (@long_v2 T r)
  end.

Eval compute in long_v2 liste1.

(*|
**Remarque:**
Coq n'est pas limité aux fonctions primitives récursives. Par exemple, la `fonction d'Ackermann <https://mathworld.wolfram.com/AckermannFunction.html>`_ peut être définie comme ci-dessous et il serait possible de démontrer qu'elle est identique à la définition usuelle:

.. image:: https://mathworld.wolfram.com/images/equations/AckermannFunction/NumberedEquation1.svg
|*)

Fixpoint pow (f:nat->nat) n a :=
  match n with
    0 => a
  | S p => pow f p (f a)
  end.

Fixpoint ack a b : nat :=
match a with
| 0 => S b
| S a => pow (ack a) (S b) 1
end.

Eval compute in (ack 3 4).            

(*|
Schémas inductifs
-----------------

Preuve par récurence sur les entiers naturels (construits avec Zero, Succ)

Est-ce que la fonction suivante (ou son type) vous rappellent quelque chose ?

.. code-block:: Coq

   Fixpoint entier_nat_ind (P : entier_nat -> Prop)
   (fZero : P Zero) (fSucc : forall n : entier_nat, P n -> P (Succ n))
   (n : entier_nat) : P n :=
     match n with
     | Zero => fZero
     | Succ n => fSucc n (entier_nat_ind P fZero fSucc n)
     end.

qui a pour type :
|*)

Check entier_nat_ind.
(* .unfold *)

(*|
Il s'agit du "Principe d’induction" pour les entiers naturels, généré
automatiquement par Coq.

(Et il se trouve que le "code" qui implémente ce principe correspond à
l'itérateur le plus général sur le type `entier_nat` :)

Le type en question est donc :

.. code-block:: Coq

   forall P : entier_nat -> Prop, P Zero ->
     (forall n : entier_nat, P n -> P (Succ n))
   -> forall n : entier_nat, P n.
|*)

(*|
Un peu d’intuition sur ce principe d’induction
----------------------------------------------

-  Hypothèses :

   -  pZero : preuve de P Zero
   -  pSucc : preuve de :math:`\forall n,\ P n \implies P (n+1)`

-  Conclusion :

   -  :math:`\forall n,\ P n`

On peut l'écrire sous la forme d'une "Règle d'inférence" :

.. code-block:: Coq

   (pZero : P Zero)  (pSucc : forall n : entier_nat, P n -> P (Succ n))
   --------------------------------------------------------------------
        entier_nat_ind P pZero pSucc :  forall n : entier_nat, P n
|*)

(*|
L'effet domino
--------------

Une petite image vaut mieux qu'un long discours :

.. image:: https://upload.wikimedia.org/wikipedia/commons/9/92/Dominoeffect.png
   :alt: CC BY-SA 3.0
   :target: https://commons.wikimedia.org/wiki/File:Dominoeffect.png
|*)

(*|
Le type inductif des listes (prédéfini)
---------------------------------------
|*)

Require Import List.
Import ListNotations.
(* Set Implicit Arguments. (* déjà fait auparavant *) *)

Check list.
(* .unfold *)

Print list.
(* .unfold *)

(*|
.. code-block:: Coq

   Fixpoint list_ind T (P : list T -> Prop)
   (pNil : P nil) (pCons : forall x l, P l -> P (x :: l)) l
   : P l :=
     match l with
     | [] => pNil
     | x :: r => pCons x r (@list_ind T P pNil pCons r)
     end.

Généré automatiquement !

Permet la "preuve par induction" sur les listes (construites avec `[]` et `::`)
|*)

(*|
Règle d'inférence du schéma inductif des listes
-----------------------------------------------

.. code-block:: Coq

   (pNil : P [])  (pCons : forall x l, P l -> P (x :: l))
   ------------------------------------------------------
           list_ind P pNil pCons :  forall l, P l

Ici, on a omis les types implicites (le param. de généricité T) par simplicité.
|*)

(*|

Correspondance entre les types et les formules logiques
-------------------------------------------------------

La correspondance de Curry–Howard : double lecture
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

+--------------------+--------------------------------+------------------------+
| Notation           | Lecture fonctionnelle          | Lecture logique        |
+====================+================================+========================+
| `x : T`            | `x` a pour type `T`            | `x` "preuve" de `T`    |
+--------------------+--------------------------------+------------------------+
| *aucun* `x:T`      | le type `T` est vide           | `T` est insatisfiable  |
+--------------------+--------------------------------+------------------------+
| `P -> Q`           | type des fonctions de P dans Q | l'implication logique  |
+--------------------+--------------------------------+------------------------+
| `f : P -> Q`       | f est une fonction de P dans Q | f preuve de ``P => Q`` |
+--------------------+--------------------------------+------------------------+
|                    | f transforme une "preuve" de P en une "preuve" de Q     |
+--------------------+--------------------------------+------------------------+
| `forall T, T -> T` | type générique de l'identité   | exemple de tautologie  |
+--------------------+--------------------------------+------------------------+
| `forall n, n+1 > n`| fonction associant à chaque    | quantification         |
|                    | entier une preuve              | universelle            |
+--------------------+--------------------------------+------------------------+
| `forall x : X, P x`| fonction dont le type          | ∀x∈X, P x              |
|                    | d'arrivée dépend de l'argument |                        |
+--------------------+--------------------------------+------------------------+

| Remarque :
| en Coq et contrairement à la "théorie des ensembles",
| toutes les variables quantifiées sont associées à un type (qui peut
  cependant être inféré :)
|*)

Check forall n, n + 1 > n.
(* .unfold *)

(*|
Exemple de types inductifs : propositions logiques
--------------------------------------------------

La Conjonction
~~~~~~~~~~~~~~

.. code-block:: Coq

   Inductive and (P Q : Prop) : Prop :=
     Conj (p : P) (q : Q).

   -->

     (p : P)  (q : Q)
   --------------------
    Conj p q :  P /\ Q

La Disjonction
~~~~~~~~~~~~~~

.. code-block:: Coq

   Inductive or (P Q: Prop): Prop :=
     | Or1 (p: P)
     | Or2 (q: Q).

   -->

         p : P              q : Q
   -----------------  -----------------
    Or1 p :  P \/ Q    Or2 q :  P \/ Q
|*)

(*|
La proposition True
~~~~~~~~~~~~~~~~~~~

.. code-block:: Coq

   Inductive True : Prop := I.  -->  ----------
                                      I : True

La proposition False
~~~~~~~~~~~~~~~~~~~~

.. code-block:: Coq

   Inductive False : Prop := .  -->  pas de preuve de `False` !
|*)

(*|
Et la quantification existentielle ?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: Coq

   Inductive ex T (P: T -> Prop) :=
     ex_intro (t: T) (p: P t).

   -->

             (t : T)  (p : P t)
   ----------------------------------------
    @ex_intro T P t p :  exists x : T, P x
|*)

(*|
À suivre au prochain cours
--------------------------

- Retour sur la correspondance de Curry-Howard
- | Présentation des "tactiques Coq"
  | pour construire une preuve interactivement/semi-automatiquement !
|*)
