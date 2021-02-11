(* https://plv.csail.mit.edu/blog/alectryon.html#using-alectryon *)

Require Import List.

Import ListNotations.


(*|
=======
 Title
=======

Prose. *Emphasis*; **strong emphasis**; ``code``; `coq code`; `link <url>`__.
|*)


(* regular comment *)

(** Coqdoc comment *)


(*|
.. note::

   More text.

.. coq::
|*)
Lemma app_nil : forall T (l1 : list T), l1 ++ [] = l1.
  (* C-c C-a TAB (dans Emacs/PG) *)
  intros T l1.
  induction l1.
  { easy. }
  simpl; rewrite IHl1.
  easy.
Qed.
