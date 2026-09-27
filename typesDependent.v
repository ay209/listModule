Require Import List.
Import ListNotations.
From Equations Require Import Equations.

Fixpoint sum (l1 l2 : list nat) : (list nat) :=
match l1, l2 with
| nil, nil => nil
| e1 :: tl1, e2 :: tl2 => (e1 + e2) :: (sum tl1 tl2)
| _, _ => nil
end.

Definition l1 := [1;2;3].
Definition l2 := [4;5].

Compute (sum l1 l1).
Compute (sum l1 l2).

Fixpoint sum2 (l1 l2 : list nat) : option (list nat) :=
match l1, l2 with
| nil, nil => Some nil
| e1 :: tl1, e2 :: tl2 =>
  match (sum2 tl1 tl2) with
  | None => None
  | Some l => Some ((e1 + e2 : nat) :: (l : list nat))
end
| _, _ => None
end.
Compute (sum2 l1 l1).
Compute (sum2 l1 l2).

(*Use dependent types to ensure that the parameters passed have the some type*)

Inductive ilist : nat -> Set :=
| Nil : ilist 0
| Cons : forall  (n m : nat), ilist n -> ilist (S n).

Definition l0 := Nil.
Check l0.

Definition l3 := Cons 2 1 (Cons 1 2 (Cons 0 3 Nil)).
Check l3.

Arguments Cons : default implicits.
(* Arguments Cons {A} _ _ is used to set implicit arguments
Here A means make the type argument A implicit
meaning Coq will infer it automatically
The other arguments _ _ are explicit
They need to be provided*)

Print Implicit Cons.

Definition l4 := Cons 1 (Cons 2 (Cons 3 Nil)).
Check l4.
Arguments Cons : clear implicits. (*Reverting back to defaults*)

Fixpoint map (f : nat -> nat) (n : nat) (l : ilist n) : (ilist n) :=
match l with
| Nil => Nil
| (Cons n e tl) => Cons n (f e) (map f n tl)
end.

Arguments map : default implicits.
(* We dont need  to provide the (n : nat) because it will be inferred
thanks to the default implicits, Coq knows this because ilist will have an
argument of type nat. *)
Print Implicit map.

Definition succ (n: nat) : nat := (S n).

Compute (map succ l4).


(*Using annotations this time
The principal is that I match something
below the example is ilist n
I may choose whatever I'd like to return when this is matched
E.g.
I matched a list of length 4, I may return 16
ilist (n * n)
The only constraint is that each constructors in the match
must respect this constraint.
*)

Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) :
ilist (n1 + n2) :=
match ls1 with
| Nil => ls2
| Cons n x tl => Cons (n + n2) x (app n tl n2 ls2)
end.

Arguments app : default implicits.

Definition l5 := Cons 1 4 (Cons 0 5 Nil).
Compute (app l4 l5).
Definition toto (l : ilist 5) := l.
Check toto(app l4 l5).
Check app l4 l5.

Parameter n : nat.
Parameter a : ilist (n + 1).
Parameter b : ilist (1 + n).

Check (a = b).

 




(*Le type de retour unit ici c'est un dummy value
On peut pas utiliser Nil -> it has no head element
We cant return a nat either because there isn't a nat to return
And we can not return None either because the return type
in the Cons case is of type nat*)
Definition hd' n (ls : ilist n) :=
match ls in (ilist n) return (match n with O => unit | S _ => nat end) with
| Nil => tt
| Cons _ h _ => h
end.

Definition hd n (ls : ilist (S n)) : nat := hd' (S n) ls.
(*Le type de hd 
Pour tout n nat, ilist S n -> nat
Also n here is not that important
We need it to be able to write ilist (S n)
That is why we use default implicit again &
tell coq to infer it directly*)


Compute (hd 2 l4).

Arguments hd : default implicits.

Compute (hd l5).
Compute (hd l3).
Compute (hd l4).
Require Import Arith.
(*
Another advantage of using dependent types here is that
if there is an error case, e.g. an empty list
The error will be caught at compile time, where as
if we were to define hd using option nat for example
The error would be caught at run time

So if the program is run that assures that there are no empty
lists.
*)
From Equations Require Import Equations.
Check Nat.eq_dec.
Print sumbool.
Definition inspect {A} (a : A) : {b | a = b}.
Proof. eauto. Defined.


(* will give an eror cuz Coq does not know
that n0 and n1 are equal

Fixpoint sum3 n (l1 l2 : ilist n) : ilist n :=
match l1 with
| Nil =>
  match l2 with
    | Nil => Nil
    | _ => Nil
  end
| Cons n0 e1 tl1 as l =>
  match l2 with
    | Nil => l
    | Cons n1 e2 tl2 =>
      match (Nat.eq_dec n0 n1) with
        | left _ => Cons n0 (e1 + e2) (sum3 n0 tl1 tl2)
        | right _ => l
      end
    end
  end.
*)





Print ilist.
Fixpoint sum3 (n : nat) (H H0 : (ilist n)) : ilist n.
Proof.
intros.
(* Cas de base de l1 *)

elim H; intros; clear H.
elim H0; intros; clear H0.
exact Nil.
exact Nil.

(* Cas inductif de l1 *)

elim H0; intros; clear H0.
exact (Cons n0 m i).
elim (Nat.eq_dec n0 n1); intros.
rewrite <- a in i0.
exact (Cons n0 (m + m0) (sum3 n0 i i0)).
exact H.
Defined.
Arguments sum3 : default implicits.

Compute (sum3 l5 l5).

(*Reecriture solution below
- give a name to the left constructor so that it may be used later
- define a new variable tl2' wherein we have
   - a function to rewrite called eq_rec_r
   - we pass to it where we want to do the reecriture with (fun t : nat => ilist t)
   - for whom, here tl2
   - and for what value, it is p: n0 = n1
   - and since we have eq_rec_r, the reecriture will be done from right to left
   - so any time we see n1, we will replace it with n0
- at the end, the recursive call will be correctly typed *)

Fixpoint sum4 n (l1 l2 : ilist n) : ilist n :=
match l1 with
| Nil =>
  match l2 with
  | Nil => Nil
  | _ => Nil
  end
| Cons n0 e1 tl1 as l =>
  match l2 with
    | Nil => l
    | Cons n1 e2 tl2 =>
      match (Nat.eq_dec n0 n1) with
        | left p =>
          let tl2' := eq_rec_r (fun t : nat => ilist t) tl2 p in
          Cons n0 (e1 + e2) (sum4 n0 tl1 tl2')
        | right _ => l
      end
     end
    end.

Arguments sum4 : default implicits.

Compute (sum4 l5 l5).


Equations sum5 (l1 l2 : list nat) : list nat :=
sum5 nil nil := nil;
sum5 (a1 :: l1) (a2 :: l2) := (a1 + a2) :: (sum5 l1 l2);
sum5 _ _ := nil.

Equations sum6 (l1 l2 : list nat) : option (list nat) :=
sum6 nil nil := Some nil;
sum6 (a1 :: l1) (a2 :: l2) with sum6 l1 l2 := 
{
  | Some l => Some ((a1 + a2) :: l)
  | None => None
};
sum6 _ _ := None.

Equations sum7 (n : nat) (l1 l2 : ilist n) : ilist n :=
sum7 _ Nil Nil := Nil;
sum7 _ (Cons n0 e1 tl1) (Cons _ e2 tl2) := Cons n0 (e1 + e2) (sum7 n0 tl1 tl2).

Equations map2 (f : nat -> nat) (n : nat) (l : ilist n) : (ilist n) :=
map2 _ _ Nil := Nil;
map2 _ _ (Cons n0 e tl) := Cons n0 (f e) (map2 f n0 tl). 

Equations app2 (n1: nat) (ls1 : ilist n1) (n2: nat) (ls2 : ilist n2) :
ilist (n1 + n2) :=
app2 _ Nil n2 ls2 := ls2;
app2 _ (Cons n x tl) n2 ls2 := Cons (n + n2) x (app2 n tl n2 ls2).

Equations hd'' (n : nat) (ls : ilist n) : match n with O => unit | S _ => nat end :=
hd'' 0 Nil := tt;
hd'' (S _) (Cons _ h _) := h.
