(*|
====================================
TAPFA - Partie Coq - Preuve assistée
====================================

:Auteurs: Jean-Paul Bodeveix (resp. UE), Erik Martin-Dorel, Pierre Roux
:Date:    L3 Info, Semestre 6, Année 2021-2022

Supports de ce cours :

-  https://pfitaxel.github.io/tapfa-coq-alectryon/

Principe
========

-  Prouver une propriété `P` :math:`\equiv` Construire un terme de type `P`.

.. coq::
|*)
Parameters (p : Prop) (q : Prop).

Theorem th : p -> (p -> q) -> q.
Proof.
exact (fun (x : p) (f : p -> q) => f x).
Qed.
(*|

-  Les tactiques aident à la construction du terme de preuve:

.. coq::
|*)
Theorem th' : p -> (p -> q) -> q.
Proof.
auto.
Qed.

Print th'.
(* .unfold *)
(*|

Les principales tactiques de preuve
===================================

La tactique `intro` (variante : `intros H_1 … H_n`)
---------------------------------------------------

.. code-block:: Coq

   h_1 : e_1                       h_1 : e_1
      ...        --> intro H -->      ...
   h_n : e_n                       h_n : e_n
   =========                       H : p
   p -> q                          =========
                                   q


   h_1 : e_1                       h_1 : e_1
      ...        --> intro x -->      ...
   h_n : e_n                       h_n : e_n
   ============                    x : t
   ∀ x : t, P x                    =========
                                   P x

Cas d’utilisation de `intro`

Lorsque le but est une implication ou une
quantification universelle :math:`\leadsto` introduction de l’hypothèse
dans le contexte
|*)

(*|
Preuve d’une égalité
--------------------

.. code-block:: Coq

   Γ        --> reflexivity -->   ∅ si t = t'
   ======
   t = t'

Cas d’utilisation de `reflexivity`

Lorsque le but est une égalité
entre 2 termes identiques (modulo calcul) :math:`\leadsto` fin de la
preuve.

Exemple

.. code-block:: Coq

   Γ          --> reflexivity -->   ∅ (Qed)
   =========
   1 + 1 = 2
|*)

(*|
Réécriture (utilisation d’une égalité)
--------------------------------------

Soit `E : t1 = t2` un théorème ou une hypothèse du contexte :math:`\Gamma`

.. code-block:: Coq

   Γ     --> rewrite E -->   Γ
   ====                      ====
   P t1                      P t2


   Γ     --> rewrite <-E -->   Γ
   ====                        ====
   P t2                        P t1


   Γ                                   Γ
   H : P t1   --> rewrite E in H -->   H : P t2
   ========                            ========
   G                                   G


   Γ                                     Γ
   H : P t2   --> rewrite <-E in H -->   H : P t1
   ========                              ========
   G                                     G
|*)

(*|
Réécriture (exemple)
--------------------
 *)

Theorem exemple_de_propriete_prouvee_par_reecriture :
  forall f : nat -> nat,
    (forall n : nat, f n = f (S n)) ->
    f 2 = f 0.
Proof.
  intros f.
  intros H.
  rewrite <- H.
  rewrite <- H.
  reflexivity.
Qed.

(*|
Réécriture (cas général où le théorème ``E`` a des conditions)
--------------------------------------------------------------

Soit
`E : ∀ x1 ... xk,
p1 x1 ... xk -> ⋅⋅⋅ -> pn x1 ... xk ->
t x1 ... xk = t' x1 ... xk`,
un théorème ou une hypothèse du contexte :math:`\Gamma`

.. code-block:: Coq

   Γ                 --> rewrite E -->   Γ
   ===============                       ================
   P (t u1 ... uk)                       P (t' u1 ... uk)

                                         Γ
                                         ============
                                         p1 u1 ... uk

                                         ...

                                         Γ
                                         ============
                                         pn u1 ... uk

                                         (* n conditions requises par le théorème E *)
|*)

(*|
Réécriture (exemple avec une condition)
---------------------------------------

.. code-block:: Coq

   pred : nat -> nat                             pred : nat -> nat
   E : ∀ x : nat, O < x ->                       E : ∀ x : nat, O < x ->
       S (pred x) = x                                S (pred x) = x
   n : nat                   --> rewrite E -->   n : nat
   =======================                       =======================
   S (pred (2 * (n + 1)))                        2 * (n + 1) = 2 * n + 2
   = 2 * n + 2
                                                 pred : nat -> nat
                                                 E : ∀ x : nat, O < x ->
                                                     S (pred x) = x
                                                 n : nat
                                                 ===============
                                                 O < 2 * (n + 1)
|*)

(*|
La tactique `apply` (variante : `apply H with (x_i:=v_i)` …)
------------------------------------------------------------

Soit `H : ∀ x1 ... xk,
p1 x1 ... xk -> ⋅⋅⋅ -> pn x1 ... xk ->
q x1 ... xk`,
un théorème ou une hypothèse du contexte :math:`\Gamma`

.. code-block:: Coq

   Γ             --> apply H -->   Γ
   ===========                     ============
   q u1 ... uk                     p1 u1 ... uk

                                   ...

                                   Γ
                                   ============
                                   pn u1 ... uk

                                   (* n conditions requises pour appliquer H *)
|*)

(*|
La tactique `apply` (exemple)
-----------------------------

.. coq::
|*)
Search concl:(_ <= _) S.
(* .unfold *)
(*|
(`documentation de la commande Search <https://coq.github.io/doc/V8.12.2/refman/proof-engine/vernacular-commands.html#coq:cmd.search>`_)
|*)

Goal forall n, n <= S (S n).
Proof.
intro n.
Check le_S.  (* réaffichons le lemme le_S, juste pour rappel *)
apply le_S.
Abort.
(*|

La tactique `induction` : applique le théorème d’induction
----------------------------------------------------------

.. coq::
|*)
Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
induction n.
Abort.
(*|

La tactique `destruct` : preuve par cas
---------------------------------------

.. coq::
|*)
Theorem addn1_neq0 : forall n : nat, n + 1 <> 0.
Proof.
destruct n.
(*|

La tactique `simpl` : simplification du but
-------------------------------------------

.. coq::
|*)
simpl.
Abort.
(*|

Détail : réduction des expressions `0+n`, `1+n`, `n+0`, `n+1`
-------------------------------------------------------------

Étant donnée que la fonction `(fun a b : nat => a + b)` est
définie récursivement par rapport à son premier argument :

-  `0 + n` se réduit par calcul à `n`

-  `1 + n` se réduit par calcul à `S n`

-  :math:`\leadsto` donc on peut prouver trivialement `1 + n = S n` (par réflexivité)

-  mais **on a besoin d’une preuve par induction** pour montrer que

   .. code-block:: Coq

      ∀ n : nat, n + 0 = n
      ∀ n : nat, n + 1 = S n

Autres tactiques non détaillées dans ces transparents :

-  `exact`

-  `symmetry`, `transitivity`

-  `constructor`, `split`, `left`, `right`, `exists`,
   `discriminate`, `injection`

-  `unfold`

-  `lia` (Linear Integer Arithmetic), `tauto`, `firstorder`

Pour plus de détails, voir l’Aide-mémoire des tactiques de preuve Coq
|*)

(*|
Retour sur la correspondance "preuve-programme" (Curry-Howard)
--------------------------------------------------------------

Coq fournit un langage de tactiques qui permet de construire
**interactivement** et **incrémentalement**, un programme fonctionnel
(le "terme de preuve").  Lorsque la construction de ce programme est
terminée, son type est vérifié par Coq au moment du `Qed` par rapport
au type attendu (c.-à-d. par rapport à la formule logique qui devait
être démontrée).

L'exemple qui suit, qui peut être joué dans la dernière version de
ProofGeneral en activant deux fonctionnalités spécifiques dans l'IDE,
illustre ce principe :

-  Menu ``Coq > Show Proof`` (``M-x coq-show-proof-stepwise-toggle RET``)
-  Menu ``Coq > Diffs > On`` (``ESC ` c D O``)

(en utilisant aussi si besoin, le menu ``Coq > Toggle 3 Windows mode``
ainsi que le raccourci ``C-c C-l  C-c C-p``)
|*)

Lemma example :
  forall A B C : Prop,
    (A -> B -> C) -> (A /\ B -> C).
Proof.
  intros A B C. (* notez l'apparition d'un fun ... *)
  intros hABC.
  intros hAB.
  destruct hAB. (* notez l'apparition d'un match-with ... *)
  apply hABC; auto.
Qed.

(*|
Exemples et exercices autour des listes
=======================================

Préliminaires
-------------

Pour charger la bibliothèque des listes (et les notations
à la OCaml) puis activer les arguments implicites pour vos définitions,
ajoutez au début de votre fichier :

.. coq::
|*)
Require Import List.
Import ListNotations.
Set Implicit Arguments.
(*|

Quelques preuves (de théorèmes de la stdlib) sur les listes
-----------------------------------------------------------

**But** Prouver que la double inversion d’une liste renvoie la liste
inchangée :

.. code-block:: Coq

   ∀ T (l : list T), rev (rev l) = l

La fonction `List.rev` est définie comme suit :

.. code-block:: Coq

   Fixpoint rev (T : Type) (l : list T) :=
     match l with
     | [] => []
     | x :: l’ => rev l’ ++ [x]
     end.

où `++` est une notation Coq qui équivaut à ``@`` en OCaml.

**Méthode** On part du théorème à prouver et on identifie au fur et à
mesure les lemmes intermédiaires qui méritent d’être prouvés à part.
|*)

(*|
Premier lemme
-------------

Prouver (par induction sur la liste `l1`) que l’on a :

.. code-block:: Coq

   Lemma app_nil : forall (T : Type) (l : list T), l = l ++ [].

Rappel: la fonction `(fun l1 l2 => l1 ++ l2)` est définie comme suit :

.. code-block:: Coq

   Fixpoint app (T : Type) (l1 l2 : list T) :=
     match l1 with
     | [] => l2
     | x1 :: l1 => x1 :: app l1 l2
     end.

Sauriez vous l'écrire en OCaml ?
|*)

(*|
Premier lemme – preuve par induction
------------------------------------

À la main :

Prouvons le lemme `app_nil` par induction structurelle sur la liste `l`.

- Cas de base (si `l` est la liste vide `[]`). On doit montrer que
  `[] = [] ++ []`, soit, après simplification de la définition de `app`,
  `[] = []`. CQFD.

- Cas inductif (si `l` est de la forme `x :: l'`).
  Fixons un `x : T` et un `l' : list T`, supposons que `l' = l' ++ []`
  et appelons cette hypothèse d'induction `IHl`.
  Montrons qu'alors `x :: l' = (x :: l') ++ []`.
  En simplifiant la définition de `app` on doit donc prouver que
  `x :: l' = x :: (l' ++ [])`, soit après avoir utilisé `IHl`, que
  `x :: l' = x :: l'`. CQFD.

Premier lemme – preuve par induction (version Coq)
--------------------------------------------------

.. coq::
|*)
Lemma app_nil : forall (T : Type) (l : list T), l = l ++ [].
Proof.
induction l.
{ (* accolades conseillées pour délimiter les preuves du sous but *)
  simpl.
  reflexivity. }
simpl.
rewrite <- IHl. (* utilise l’hypothèse d’induction *)
reflexivity.
Qed.
(*|

Pour appliquer `simpl` à chaque sous-but généré il suffit d’écrire
la tactique une fois après ";"

.. coq::
|*)
Lemma app_nil' : forall (T : Type) (l : list T), l = l ++ [].
Proof.
induction l; simpl.
{ reflexivity. }
rewrite <- IHl. (* utilise l’hypothèse d’induction *)
reflexivity.
Qed.
(*|

Deuxième lemme
--------------

.. coq::
|*)
Lemma app_assoc :
  forall T (l1 l2 l3 : list T), l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
induction l1; simpl; intros; auto.
rewrite IHl1.
reflexivity.
Qed.
(*|

`auto` essaie d’appliquer récursivement les hypothèses
(et certains lemmes standard, comme la réflexivité)
pour prouver le sous-but ; sinon la tactique ne fait rien.

Troisième lemme
---------------

.. coq::
|*)
Lemma rev_app_distr :
  forall T (l1 l2 : list T), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
induction l1; simpl; intros.
apply app_nil.
rewrite IHl1.
rewrite app_assoc.
reflexivity.
Qed.
(*|

Le théorème visé
----------------

.. coq::
|*)
Theorem rev_involutive : forall T (l : list T), rev (rev l) = l.
Proof.
(* exercice ! *)
(* Qed. *)
