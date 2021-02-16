(*|
======================================================
Types Abstraits et Programmation Fonctionnelle Avancée
======================================================

:Auteurs: Jean-Paul Bodeveix (resp. UE), Erik Martin-Dorel, Pierre Roux
:Date:    L3 Info, Semestre 6, Année 2020-2021

Supports de ce cours :

-  https://pfitaxel.github.io/tapfa-coq-alectryon/

Principe
========

-  Prouver une propriété :math:`P` :math:`\equiv` Construire un terme de
   type :math:`P`.

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
(*|

Les principales tactiques de preuve
===================================

La tactique intro (variante : intros H\ :math:`_1` … H\ :math:`_n`)
-------------------------------------------------------------------

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

Réécriture (utilisation d’une égalité)
--------------------------------------

Soit ``E`` : :math:`t_1=t_2` un théorème ou une hypothèse du contexte
:math:`\Gamma`

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

Réécriture (cas général où le théorème ``E`` a des conditions)
--------------------------------------------------------------

Soit
:math:`\mathtt{E}: \forall x_1 \ldots x_k,-p_1-x_1 \ldots x_k\rightarrow \cdots
\rightarrow p_n-x_1\ldots x_k\rightarrow t-x_1\ldots x_k = t'-x_1\ldots
x_k`
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

La tactique apply (variante: apply H with (:math:`x_i`:=:math:`v_i`) …)
-----------------------------------------------------------------------

Soit ``H`` :
:math:`\forall x_1 \ldots x_k,-p_1-x_1\ldots x_k\rightarrow \cdots
\rightarrow p_n-x_1\ldots x_k\rightarrow q-x_1\ldots x_k`
un théorème ou une hypothèse du contexte :math:`\Gamma`

.. code-block:: Coq

   Γ             --> apply H -->   Γ
   ===========                     ============
   q u1 ... uk                     p1 u1 ... uk

                                   ...

                                   Γ
                                   ============
                                   pn u1 ... uk

La tactique apply (exemple)
---------------------------

.. coq::
|*)
Search concl:(_ <= _) S.
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

La tactique induction : applique le théorème d’induction
--------------------------------------------------------

.. coq::
|*)
Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
induction n.
Abort.
(*|

La tactique destruct : preuve par cas
-------------------------------------

.. coq::
|*)
Theorem addn1_neq0 : forall n : nat, n + 1 <> 0.
Proof.
destruct n.
(*|

La tactique simpl : simplification du but
-----------------------------------------

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

Autres tactiques Autres tactiques non détaillées dans ces transparents :

-  `exact`

-  `symmetry`, `transitivity`

-  `constructor`, `split`, `left`, `right`, `exists`,
   `discriminate`, `injection`

-  `unfold`

-  `lia` (Linear Integer Arithmetic), `tauto`, `firstorder`

Pour plus de détails, voir l’Aide-mémoire des tactiques de preuve Coq

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

Premier lemme – preuve par induction
------------------------------------

À la main :

Prouvons le lemme `app_nil` par induction structurelle sur la liste `l`.

- Si `l` est la liste vide `[]`, on a bien `[] = [] ++ []`
  en simplifiant la définition de `app`.

- Sinon, `l` est de la forme `x :: l'`. En supposant que `l' = l' ++ []`
  (appelons cette hypothèse d'induction `IHl`), montrons que
  `x :: l' = (x :: l') ++ []`. En simplifiant la définition de `app`
  on doit donc prouver que `x :: l' = x :: (l' ++ [])`, soit en appliquant
  `IHl`, que `x :: l' = x :: l'`.

En Coq :

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
(* TODO *)
(* Qed. *)
