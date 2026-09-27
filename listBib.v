(* listBib.v
  A library of lists of length n (ilist n), inspired by OCaml's List
  module and written with the Equations plugin.
*)
Module IList.
Require Import Arith.
From Equations Require Import Equations.
Import EqNotations.
Require Import Lia.
Require Import Program.Equality.
Require Import Bool.
Require Import List.
Import ListNotations.

(*ilist est utilisée pour créér des listes
type dépendent pour avoir compile time
type safety.*)
Inductive ilist : nat -> Type :=
| Nil : ilist 0
| Cons : forall (n: nat), nat -> ilist n -> ilist (S n).

(*Définition de la fonction de la permutation*)
Inductive perm : list nat -> list nat -> Prop :=
| perm_nil : perm nil nil
| perm_skip : forall x l1 l2, perm l1 l2 -> perm (x :: l1) (x :: l2)
| perm_swap : forall x y l, perm (x :: y :: l) (y :: x :: l)
| perm_trans : forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

(*On rend implicite le premier argument
du constructeur Cons dans ilist.*)
Arguments Cons {n} _ _.

Definition length (n : nat) (ls : ilist n) : nat := n.

(*Le début des définitions avec le plugin Equations*)

(*-------------------------------------*)

(*La fonction hd qui prend une liste ls non vide et
renvoie son premier élément.*)
Equations hd (n : nat) (ls : ilist (S n)) : nat :=
hd _ (Cons h _) := h.

(*La fonction tl qui prend une liste ls non vide et
renvoie sa queue.*)
Equations tl (n : nat) (ls : ilist (S n)) : ilist n :=
tl _ (Cons _ t) := t.

(*La fonction n_th qui prend une liste ls et un index i,
renvoie l'élément se trouvant à cet indice s'il existe.*)
Equations n_th (n i : nat) (ls :ilist n) : option nat :=
n_th _ _ Nil := None;
n_th _ 0 (Cons h tl) := Some h;
n_th _ (S i) (Cons h tl) := n_th _ i tl.

(*La fonction map qui prend une fonction f et une list ls,
applique la fonction f aux éléments de cette liste ls,
et renvoie la nouvelle liste obtenue. *)
Equations map (n : nat) (f: nat -> nat) (ls : ilist n) : ilist n :=
map _ _ Nil := Nil;
map _ f (Cons h tl) := Cons (f h) (map _ f tl).

(*La fonction isnoc est un auxilaire pour la fonction rev.
Elle prend une liste ls et un entier e,
met cet entier à la fin de cette liste.*)
Equations isnoc (n : nat) (ls : ilist n) (e : nat) : ilist (S n) :=
isnoc _ Nil e := Cons e Nil;
isnoc _ (Cons h tl) e := Cons h (isnoc _ tl e).

(*La fonction rev prend une liste ls et
inverse les éléments de cette liste.*)
Equations rev (n : nat) (ls : ilist n) : ilist n :=
rev _ Nil := Nil;
rev _ (Cons h tl) := isnoc _ (rev _ tl ) h.

(*La fonction app prend deux listes l1 l2,
et renvoie la concaténation de ces deux listes.*)
Equations app (n1: nat) (l1 : ilist n1) (n2: nat) (l2 : ilist n2) : ilist (n1+n2) :=
app _ Nil _ l2 := l2;
app _ (Cons h1 tl1) _ ls2 := Cons h1 (app _ tl1 _ ls2).

(*La fonction filter prend en entrée une fonction f et
une liste l, vérifie la propriété f pour chaque élément de cette liste.
Elle renvoie une nouvelle liste qui contient les éléments de l
vérifiant cette propriété.*)
Equations filter (n: nat) (f: nat -> bool) (l : ilist n) : list nat :=
filter _ _ Nil := nil ;
filter _ f (Cons h tl) with f h := { 
|true => cons h (filter _ f tl)
|false => filter _ f tl
}.

(*La fonction fold_right applique f à chaque élément de l
de droite à gauche, en partant avec la valeur de base b. Retourne :
f a1 (f a2 ( ... ( f an b )))*)
Equations fold_right {B : Type} (n: nat) (f: nat -> B -> B) (b: B) (l: ilist n) : B :=
fold_right _ _ a Nil := a;
fold_right _ f a (Cons h tl) := f h (fold_right _ f a tl). 

(*La fonction fold_left applique f à chaque élément de l
de gauche à droite, en partant de b. Retourne :
f( ... f(f b a1) a2 ... ) an.*)
Equations fold_left {B : Type} (n: nat) (f: B -> nat -> B) (b: B) (l :ilist n) : B :=
fold_left _ _ a Nil := a;
fold_left _ f a (Cons h tl) := fold_left _ f (f a h) tl.

(*La fonction _exists retourne vrai s'il existe un
élément dans l vérifiant f.*)
Equations _exists (n: nat) (f: nat -> bool) (l: ilist n) : bool :=
_exists _ _ Nil := false;
_exists _ f (Cons h tl) := (f h) || (_exists _ f tl).

(*La fonction for_all retourne vrai si
chaque élément de l vérifie la propriété.*)
Equations for_all (n: nat) (f: nat-> bool) (l: ilist n) : bool :=
for_all _ _ Nil := true;
for_all _ f (Cons h tl) := (f h) && (for_all _ f tl).

(*La fonction find retourne le premier élément de l
vérifiant f, ou None.*)
Equations find (n: nat) (f: nat -> bool) (l: ilist n) : option nat :=
find _ _ Nil := None;
find _ f (Cons h tl) with f h := {
| true => Some h
| false => find _ f tl}.

(*La fonction insert insère l'élément e dans la liste triée l
en gardant l'ordre.*)
Equations insert (n: nat) (e: nat) (l: ilist n) : ilist (S n) :=
insert _ e Nil := Cons e Nil;
insert _ e (Cons h tl) with Nat.leb e h :={
| true => Cons e (Cons h tl)
| false => Cons h (insert _ e tl)
}.

(*La fonction sort trie la liste l par insertion.*)
Equations sort (n : nat) (l : ilist n) : ilist n :=
sort _ Nil := Nil;
sort _ (Cons h tl) := insert _ h (sort _ tl).

(*La fonction length' calcule longueur d'une liste nat.*)
Equations length' (l : list nat) : nat :=
length' nil := 0;
length' (cons _ tl) := S (length' tl).

(*La fonction inject convertit une liste nat en ilist de même longueur.*)
Equations inject (l : list nat) : ilist (length' l) :=
inject nil := Nil;
inject (cons x tl) := Cons x (inject tl).

(*La fonction unject convertit une ilist en list nat.*)
Equations unject (n : nat) (l : ilist n) : list nat :=
unject _ Nil := nil;
unject _ (Cons h t) := cons h (unject _ t).

(* ilist2 représente une liste de k sous-listes, chacune
de même longueur. Elle est utilisée dans la fonction flatten.*)
Inductive ilist2 (n : nat) : nat -> Type :=
| Nil2 : ilist2 n 0
| Cons2 : forall (k : nat), ilist n -> ilist2 n k -> ilist2 n (S k).

(* On applatit une liste de k sous-listes de longueur n.
Ne fonctionne que si toutes les sous-listes ont la même longueur.*)
Equations flatten (n k : nat) (l: ilist2 n k) : ilist (k * n) :=
flatten _ _ Nil2 := Nil;
flatten n k (Cons2 k h tl) := app n h (k * n) (flatten n k tl).

(* On merge deux ilists de même longueur en une liste de paires.*)
Equations combine (n : nat) (l1: ilist n) (l2: ilist n) : list (nat * nat):=
combine _ Nil Nil := nil;
combine n0 (Cons h1 tl1) (Cons h2 tl2) := cons (h1, h2) (combine _ tl1 tl2).

(* Quelques Lemmes*)

(*---------------------*)

(*On concatène une liste vide à une liste.*)
Lemma app_nil : forall (n : nat) (l : ilist n), 
  unject _ (app n l 0 Nil) = unject _ l.
Proof.
intros n l.
funelim (app n l 0 Nil).
simp unject.
reflexivity.

simp app.
simpl.
simp unject.

rewrite H.
reflexivity.
Qed.


(*La concaténation est associative.*)
Lemma app_assoc : forall (n1 n2 n3 : nat) (l1 : ilist n1) (l2 : ilist n2) (l3 : ilist n3),
  unject _ (app _ (app _ l1 _ l2) _ l3) = unject _ (app _ l1 _ (app _ l2 _ l3)).
Proof.
intros.
funelim  (app n1 l1 n2 l2).
simp app.
simpl.
reflexivity.
simp app.
simpl.
simp unject.
simp app.
rewrite <- H.
reflexivity.
Qed.

(*Ajouter un élément h à une liste l1 et
faire une concaténation de cette nouvelle liste avec l2 
est équivalent à faire une concaténation de l1 et l2, 
et ajouter un élément h.*)
Lemma app_com_cons : forall (n1 n2 : nat) (l1 : ilist n1) (l2 : ilist n2) (h : nat),
  unject _ (app _ (Cons h l1) _ l2) = unject _ (Cons h (app _ l1 _ l2)).
Proof.
intros.
funelim (app n1 l1 n2 l2).
simp app.
simp unject.
reflexivity.
simp app.
simp unject.
rewrite <- H.
simpl.
reflexivity.
Qed.
(*Le résultat d'une concaténation vide implique que les deux listes sont vides.*)
Lemma app_nil_unject : forall (n1 n2 : nat) (l1 : ilist n1) (l2 : ilist n2),
  unject _ (app _ l1 _ l2) = nil ->
  unject _ l1 = nil /\ unject _ l2 = nil.
Proof.
  intros n1 n2 l1 l2 H.
  induction l1.
  - simp app in H. simp unject. split. reflexivity. exact H.
  - simp app in H. simp unject in H. discriminate H.
Qed.

(*Si la concaténation de l1 et l2 est égale à un singleton h
alors soit l1 est vide et l2  = [h], soit l1 = [h] et l2 est vide.*)
Lemma app_eq_unit : forall (n1 n2: nat) (l1 : ilist n1) (l2 : ilist n2) (h : nat),
unject _ (app _ l1 _ l2) = unject _ (Cons h Nil) -> (unject _ l1 = nil /\ unject _ l2 = cons h nil \/ unject _ l1 = cons h nil /\ unject _ l2 = nil).
Proof.
intros n1 n2 l1 l2 h H.
induction l1.
simp app in H.
simp unject in H.
simp unject.
left.
split.
reflexivity.

apply H.
simp app in H.
simp unject in H.
simpl in H.
simp unject.

simp unject in H.

injection H.
intros Htl Hh.
subst.
right. split.
apply app_nil_unject in Htl.
destruct Htl as [Hl1 _].
rewrite Hl1.
reflexivity.
apply app_nil_unject in Htl.
destruct Htl as [_ Hl2].
exact Hl2.
Qed.
(*La fonction map retourne la même liste si on lui passe
la fonction d'identité f comme paramètre.*)
Lemma map_id : forall (n : nat) (l : ilist n),
  unject _ (map n (fun x => x) l) = unject _ l.
Proof.
intros.
funelim (map n (fun x : nat => x) l).
simp unject.
simp map.
simp unject.
reflexivity.
simp map.
simp unject.
rewrite <- H.
reflexivity.
Qed.
(*Mapper une composition f rond g est équivalent à mapper g puis f.*)
Lemma map_compose : forall (n : nat) (f g : nat -> nat) (l : ilist n),
  unject _ (map n (fun x => f (g x)) l) = unject _ (map n f (map n g l)).
Proof.
intros.
funelim (map n (fun x : nat => f (g x)) l).
simp map.
reflexivity.
simp map.
simp unject.
rewrite <- H.
reflexivity.
Qed.

(*Unject d'une concaténation de deux ilist est équivalent à
la concaténation de deux listes nats.*)
Lemma unject_app : forall (n1 n2 : nat) (l1 : ilist n1) (l2 : ilist n2),
  unject _ (app _ l1 _ l2) = (unject _ l1 ++ unject _ l2).
Proof.
intros.
funelim (app n1 l1 n2 l2).
simpl.
simp unject.
simpl.
simp app.
reflexivity.
simp app.
simp unject.
simpl.
rewrite <- H.
simp unject.
reflexivity.
Qed.

(*Isnoc ajoute un élément à la fin quand c'est une liste nat.*)
Lemma isnoc_unject : forall (n : nat) (l : ilist n) (e : nat),
  unject _ (isnoc n l e) = (unject _ l ++ (e :: nil)).
Proof.
intros.
funelim (isnoc n l e).
simp isnoc.
simp unject.
simpl.
reflexivity.
simp isnoc.
simp unject.
rewrite H.
reflexivity.
Qed.

(*Map et List.map sont commutatives avec unject.*)
Lemma map_unject : forall (n : nat) (f: nat -> nat) (l : ilist n),
unject _ (map n f l) = List.map f (unject _ l).
Proof.
intros.
funelim (map n f l).
simp map.
simp unject.
reflexivity.
simp map.
simp unject.
simpl.
rewrite H.
reflexivity.
Qed.

(*La longueur de unject l est égale à la taille n.*)
Lemma unject_length : forall (n : nat) (l : ilist n),
  length' (unject n l) = n.
Proof.
intros.
funelim (unject n l).
reflexivity.
simp unject.
simpl.
rewrite length'_equation_2.
rewrite H.
reflexivity.
Qed.

(* Insérer un élément augmente la longueur de 1.*)
Lemma insert_unject : forall (n : nat) (e : nat) (l : ilist n),
  length' (unject _ (insert n e l)) = S n.
Proof.
intros.
induction l.
simp insert.
simp unject.
simpl.
reflexivity.

simp insert.
destruct (Nat.leb e n0) eqn:Heq.

simpl.
simp unject.
rewrite length'_equation_2.

simp length'.
rewrite unject_length.
reflexivity.
simpl.
simp unject.
simp length'.
rewrite unject_length.
reflexivity.
Qed.

(*Inverser une liste avec un élément à la fin le place au début.*)
Lemma rev_isnoc : forall (n : nat) (l : ilist n) (e : nat),
  unject _ (rev _ (isnoc n l e)) = 
  (e :: unject _ (rev n l)).
Proof.
intros.
funelim (isnoc n l e).
simp isnoc.
simp rev.
simp unject.
simp isnoc.
simp unject.
reflexivity.
simp isnoc.
simp rev.
rewrite isnoc_unject.
rewrite H.
rewrite isnoc_unject.
reflexivity.
Qed.


(*On obtient la même liste si on l'inverse deux fois.*)
Lemma rev_rev : forall (n: nat) (l : ilist n), unject _ (rev n (rev n l)) = unject _ l.
Proof.
intros.
funelim (rev n l).
simp rev.

reflexivity.
simp unject.

simp rev.
rewrite rev_isnoc.
rewrite H.
reflexivity.
Qed.

(*L'inverse de la concaténation de deux listes l1 et l2 est équivalent à
la concaténation de l2 et l1.*)
Lemma rev_app : forall (n1 n2 : nat) (l1 : ilist n1) (l2 : ilist n2),
  unject _ (rev _ (app _ l1 _ l2)) = 
  unject _ (app _ (rev _ l2) _ (rev _ l1)).
Proof.
intros.
funelim (app n1 l1 n2 l2).
simp app.
simp rev.
simpl.
simp unject.
rewrite app_nil.
reflexivity.
simp app.
simp rev.
simp unject.
simpl.
rewrite rev_equation_2.
rewrite isnoc_unject.
rewrite H.
rewrite unject_app.
rewrite unject_app.
rewrite isnoc_unject.
rewrite List.app_assoc.

reflexivity.
Qed.
(*Map se distribue sur app.*)
Lemma map_app : forall (n1 n2 : nat) (f : nat -> nat) (l1 : ilist n1) (l2 : ilist n2),
  unject _ (map _ f (app _ l1 _ l2)) =
  unject _ (app _ (map _ f l1) _ (map _ f l2)).
Proof.
intros.
funelim (app n1 l1 n2 l2).
simpl.
simp app.
reflexivity.
simpl.
simp map.
simp app.
simp unject.

simp unject.
simp map.

simp unject.
rewrite (H f).
reflexivity.
Qed.
(*Map et rev sont commutatives.*)
Lemma map_rev : forall (n : nat) (f : nat -> nat) (l : ilist n),
  unject _ (map n f (rev n l)) = 
  unject _ (rev n (map n f l)).
Proof.
intros.
funelim (map n f l).
simp rev.
simp map.
simp rev.
reflexivity.
rewrite map_unject.
simp map.

simp rev.
simp map.
rewrite isnoc_unject.
rewrite isnoc_unject.
rewrite List.map_app.
rewrite <- H.
simpl.
rewrite map_unject.
reflexivity.
Qed.

(* Find f l retourne le même résultat que le premier élément de la liste
obtenue en filtrant l avec f.*)
Lemma find_filter : forall (n : nat) (f : nat -> bool) (l : ilist n),
  find n f l = List.hd_error (filter n f l).
Print List.hd_error.
Proof.
intros.
funelim (find n f l).
reflexivity.

rewrite <- Heqcall.
simp filter.
rewrite Heq.
simpl.
reflexivity.
rewrite <- Heqcall.
simp filter.
rewrite Heq.
simpl.
rewrite H.
reflexivity.
Qed.

(*Le nombre d'éléments de l vérifiant f est <= à la taille de l.*)
Lemma filter_length : forall (n : nat) (f : nat -> bool) (l : ilist n),
  length' (filter n f l) <= n.
Proof.
intros.
funelim (filter n f l).
reflexivity.
rewrite <- Heqcall.
simp length'.

lia.
rewrite <- Heqcall.
lia.
Qed.

(*Le tri préserve la longueur.*)
Lemma sort_length : forall (n : nat) (l : ilist n),
  length' (unject _ (sort n l)) = n.
Proof.
intros.
funelim (sort n l).
simp sort.
simp unject.
reflexivity.
simp sort.
rewrite unject_length.
reflexivity.
Qed.

(*_exists est la négation de for_all avec le prédicat nié (negb f) faux.*)
Lemma exists_negb_for_all : forall (n : nat) (f : nat -> bool) (l : ilist n),
  _exists n f l = negb (for_all n (fun x => negb (f x)) l).
Proof.
intros.
funelim (_exists n f l).
simp for_all.
simp _exists.
simpl.
reflexivity.
simp for_all.
simp _exists.
rewrite H.
rewrite negb_andb.
rewrite negb_involutive.
reflexivity.
Qed.

(*for_all f l retourne true si et seulement si filter f l
retourne la même liste que l.*)
Lemma for_all_filter : forall (n : nat) (f : nat -> bool) (l : ilist n),
  for_all n f l = true <-> filter n f l = unject _ l.
Proof.
intros.
funelim (for_all n f l).
split.
simp filter.
simp unject.
simp for_all.
reflexivity.
simp filter.
simp unject.
simp for_all.
reflexivity.
simp for_all.
simp filter.
simp unject.
rewrite andb_true_iff.

split.
intro.
destruct H0 as [H1 H2].
rewrite H1.
simpl.

destruct H as [H3 H4].

apply H3 in H2.
rewrite H2.
reflexivity.
destruct H as [H3 H4].
simp filter.
intro.
simp filter.
split.
destruct (f h) eqn:Heq.
reflexivity.
simp filter in H.
assert (Hlen : length' (filter n0 f tl0) <= n0) by apply filter_length.
rewrite H in Hlen.

simp length' in Hlen.
rewrite unject_length in Hlen.
lia.
destruct (f h) eqn:Heq.
simpl in H.
injection H.
intro Htl.
apply H4.
apply Htl.
simpl in H.
assert (Hlen : length' (filter n0 f tl0) <= n0) by apply filter_length.
rewrite H in Hlen.
rewrite length'_equation_2 in Hlen.

rewrite unject_length in Hlen.
lia.
Qed.

(*Filtrer deux fois avec le même f est idempotent.*)
Lemma filter_filter : forall (n : nat) (f : nat -> bool) (l : ilist n),
  List.filter f (filter n f l) = filter n f l.
Proof.
intros.
funelim (filter n f l).
reflexivity.
simp filter.
rewrite Heq.
simpl.
rewrite H.
rewrite Heq.
reflexivity.
simp filter.
rewrite Heq.
simpl.
rewrite H.
reflexivity.
Qed.

(*Filtrer se distribue sur app avec la concaténation.*)
Lemma filter_app : forall (n1 n2 : nat) (f : nat -> bool) (l1 : ilist n1) (l2 : ilist n2),
filter _ f (app _ l1 _ l2) = (filter _ f l1 ++ filter _ f l2).
Proof.
intros.
induction l1.
simpl.
simp filter.
simpl.
simp app.
reflexivity.

simp app.
destruct (f n0) eqn:Heq.
simp filter.
rewrite Heq.
simpl.
rewrite <- IHl1.

simp filter.
rewrite Heq.
simpl.
reflexivity.

simp filter.
rewrite Heq.
simpl.
rewrite <- IHl1.

simp filter.
rewrite Heq.
simpl.
reflexivity.
Qed.

(* fold_left sur app l1 l2 est équivalent à
appliquer fold_left sur l1 puis sur l2 en utilisant
le résultat comme accumulateur.*)
Lemma fold_left_app : forall {B : Type} (n1 n2 : nat) (f : B -> nat -> B) (b : B) (l1 : ilist n1) (l2 : ilist n2),
  fold_left _ f b (app _ l1 _ l2) = 
  fold_left _ f (fold_left _ f b l1) l2.
Proof.
  intros B n1 n2 f b l1.
  revert b.
  induction l1.
  intros b l2.
  simp app.
  simp fold_left.
  reflexivity.
  intros b l2.
  simp app.
  simp fold_left.
  simpl.
  rewrite fold_left_equation_2.
  apply IHl1.

Qed.

(* fold_right sur app l1 l2 est équivalent à appliquer fold_right
sur l2 d'abord pour obtenir une valeur de base, ensuite appliquer
fold_right sur l1. *)
Lemma fold_right_app : forall {B : Type} (n1 n2 : nat) (f : nat -> B -> B) (b : B) (l1 : ilist n1) (l2 : ilist n2),
  fold_right _ f b (app _ l1 _ l2) = 
  fold_right _ f (fold_right _ f b l2) l1.
Proof.
intros B n1 n2 f b l1.
revert b.
induction l1.
intros b l2.
simp app.
simp fold_right.
simpl.
reflexivity.
intros b l2.
simpl.
simp app.
simp fold_right.
rewrite <- fold_right_equation_2.
rewrite <- IHl1.
simp fold_right.
reflexivity.
Qed.

(*Toute liste est une permutation d'elle-même.*)
Lemma perm_refl : forall (l : list nat), perm l l.
Proof.
  induction l.
  apply perm_nil.
  apply perm_skip. exact IHl.
Qed.

(*Insérer e dans l donne une permutation de e :: l.*)
Lemma insert_permutation : forall (n : nat) (e : nat) (l : ilist n),
  perm (unject _ (insert n e l)) (e :: unject _ l).
Proof.
intros.
funelim (insert n e l).
simp insert.
simp unject.
apply perm_skip.
apply perm_nil.
simp insert.
rewrite Heq.
simpl.
simp unject.
apply perm_refl.
simp insert.
rewrite Heq.
simpl.
simp unject.
apply perm_trans with (l2 := h :: e :: unject _ tl0).
apply perm_skip.
apply H.
apply perm_swap.
Qed.

(*Trier une liste donne une permutation de la liste 
de départ.*)
Lemma sort_permutation : forall (n : nat) (l : ilist n),
  perm (unject _ (sort n l)) (unject _ l).
Proof.
intros.
funelim (sort n l).
simp unject.
simp sort.
simp unject.
apply perm_refl.
apply perm_trans with (l2 := h :: unject n0  (sort n0 tl0) ).
simp sort.
apply insert_permutation.
simp unject.
apply perm_skip.
apply H.
Qed.

(*Convertir une list nat en ilist puis revenir en arrière donne
la même liste.*)
Lemma unject_inject : forall (l : list nat),
  unject _ (inject l) = l.
Proof.
intro.
funelim (inject l).

reflexivity.
simpl.
simp inject.
simp unject.
simp length'.

cbn [length'].
simp unject.
rewrite H.
reflexivity.
Qed.
(*inject et unject sont inverses : convertir une ilist en list nat,
puis reconvertir en ilist et revenir en list nat donne le même résultat.*)
Lemma inject_unject : forall (n : nat) (l : ilist n),
    unject _ (inject (unject n l)) = unject n l.
Proof.
intros.
funelim (unject n l).
simp unject.
reflexivity.
rewrite unject_inject.
reflexivity.
Qed.

End IList.
