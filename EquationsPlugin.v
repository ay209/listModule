(* EquationsPlugin.v
  First steps with the Equations plugin, on ordinary (non-indexed) lists.
*)
From Equations Require Import Equations.


Axiom to_fill : forall A, A.
Arguments to_fill {_}.

Inductive list A : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

Arguments nil {_}.
Arguments cons {_} _ _.
(*The A argument is implicit*)
Equations tail {A} (l : list A) : list A :=
tail nil := nil;
tail (cons a l) := l.

Equations length {A} (l : list A) : nat :=
length nil := 0;
length (cons a l) := S (length l).

Equations app {A} (l l' : list A) : list A :=
app nil l' := l';
app (cons a l) l' := cons a (app l l').

(*Creating shortcuts by using notations
and redefining the functions above*)
Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "x :: l" := (cons x l).

Equations length' {A} (l : list A) : nat :=
length' [] := 0;
length' (a :: l) := S (length' l).

Equations app' {A} (l l': list A) : list A :=
app' [] l' := l';
app' (a :: l) l' := a :: (app' l l'). 

(* Another equivalent way of defining these functions *)

Equations length'' {A} (l : list A) : nat :=
  | [] := 0
  | (a :: l) := S (length'' l).

Equations app'' {A} (l l' : list A) : list A :=
  | [] , l' := l'
  | (a :: l), l' := a :: (app'' l l').

Equations nth_option {A} (n : nat) (l : list A) : option A :=
nth_option 0 []     := None ;
nth_option 0 (a::l) := Some a ;
nth_option (S n) []     := None ;
nth_option (S n) (a::l) := nth_option n l.

Equations nth_option' {A} (l : list A) (n : nat) : option A :=
nth_option' [] _ := None;
nth_option' (a::l) 0 := Some a;
nth_option' (a::l) (S n) := nth_option' l n.


Goal forall {A} (a:A) n, nth_option n (nil (A := A)) = nth_option' (nil (A:=A)) n.
Proof.
intros.
autorewrite with nth_option.
autorewrite with nth_option'.
destruct n; reflexivity.
Qed.

Equations swap_list_pair {A B} (l : list (A * B)) : list (B * A) :=
swap_list_pair [] := [];
swap_list_pair ((a,b) :: l) := (b,a) :: (swap_list_pair l).

Equations map {A B} (f : A -> B) (l : list A) : list B :=
map _ [] := [];
map f (a :: l) := (f a) :: (map f l).

Equations head_option {A} (l : list A) : option A :=
head_option [] := None;
head_option (a :: l) := Some a.

Equations fold_right {A B} (f : A -> B -> B) (b : B) (l : list A) : B :=
fold_right f b [] := b;
fold_right f b (a :: l) := f a (fold_right f b l).

Succeed Example testing : map (Nat.add 1) (1::2::3::4::nil) = (2::3::4::5::nil)
  := eq_refl.
Succeed Example testing : @head_option nat nil = None := eq_refl.
Succeed Example testing : head_option (1::2::3::nil) = Some 1 := eq_refl.
Succeed Example testing : fold_right Nat.mul 1 (1::2::3::4::nil) = 24 := eq_refl.
Lemma nil_app {A} (l : list A) : app [] l = l.
Proof.
  (* unfold fails, and cbn has no effect 
  Fail unfold "++".*) Fail progress cbn.
  (* But reflexivity works *)
  reflexivity.
Qed.
Equations f4 (n : nat) : nat :=
f4 _ := 4.

(*By default Equations does not allow unfold to work
The command below makes it so that we may unfold f4*)
Global Transparent f4.

Goal f4 3 = 4.
Proof.
  (* f4 can now be unfolded *)
  unfold f4.
Abort.
(*We see that cbn still fails
It will not work unless it knows it is safe to reduce
Transparent just allows "the unfold" but cbn does not know
when to reduce*)
Goal f4 3 = 4.
Proof.
  (* Yet, it still cannot be simplify by cbn *)
  Fail progress cbn.
  (* Arguments enables to recover simplification 
!_ means that the argument must be a constructor or
a concrete value
/ this tells cbn that it is a valid reduction point
together they allow the reduction to happen*)
  Arguments f4 !_ /. cbn.
Abort.

Print Rewrite HintDb app.

Lemma app_nil {A} (l : list A) : app l nil = l.
Proof.
  intros; induction l. all: autorewrite with app.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma app_assoc {A} (l1 l2 l3 : list A) : app (app l1 l2) l3 = (app l1 (app l2 l3)).
Proof.
  induction l1. all: autorewrite with app.
  - reflexivity.
  - rewrite IHl1. reflexivity.
Qed.

Lemma nth_eq {A} (l : list A) (n : nat) : nth_option n l = nth_option' l n.
Proof.
  revert n; induction l; intro n; destruct n.
  all : autorewrite with nth_option nth_option'.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IHl.
Abort.

Equations half (n : nat) : nat :=
half 0 := 0 ;
half 1 := 0 ;
half (S (S n)) := S (half n).


Equations mod2 (n : nat) : nat :=
mod2 0 := 0;
mod2 1 := 1;
mod2 (S (S n)) := mod2 n.

Check half_elim. 
(*functional induction vs simple induction
- simple induction goes one step at a time
- whereas functional induction matches the function itself.
Meaning, in the example above, if we were to use a simple induction we
would be stuck since half is defined two steps at a time.*)

Lemma nth_eq {A} (l : list A) (n : nat) : nth_option n l = nth_option' l n.
Proof.
  funelim (nth_option n l).
  all: autorewrite with nth_option'.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply H.
Abort.

Definition half_mod2 (n : nat) : n = half n + half n + mod2 n.
Proof.
  induction n. 1: reflexivity.
  induction n. 1: reflexivity.
  (* We simplify the goal *)
  autorewrite with half mod2.
  rewrite PeanoNat.Nat.add_succ_r. cbn.
  f_equal. f_equal.
  (* We then get stuck as we have the wrong hypotheses *)
Abort.

Definition half_mod2 (n : nat) : n = half n + half n + mod2 n.
Proof.
  funelim (half n). 1-2: reflexivity.
  autorewrite with half mod2.
  rewrite PeanoNat.Nat.add_succ_r. cbn.
  f_equal. f_equal.
  (* We now have the good recursion hypotheses *)
  assumption.
Qed.