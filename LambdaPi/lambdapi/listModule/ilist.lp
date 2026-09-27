// Polymorphic lists, their functions and their eight lemmas.
require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Eq;
require open listModule.nat;

// A simple polymorphic list
(A : Set) inductive ilist : TYPE ≔
| Nil : ilist A
| Cons : τ A → ilist A → ilist A;

// Set-level code for ilist
// needed so that we may use = (Stdlib.Eq)
constant symbol ilistS : Set → Set;
rule τ (ilistS $A) ↪ ilist $A;

// Functions

// app: concatenation
symbol appL [A : Set] : τ (ilistS A) → τ (ilistS A) → τ (ilistS A);
rule appL Nil $l ↪ $l;
rule appL (Cons $h $tl) $l ↪ Cons $h (appL $tl $l);

// isnoc: add element at end
symbol isnocL [A : Set] : τ A → τ (ilistS A) → τ (ilistS A);
rule isnocL $e Nil ↪ Cons $e Nil;
rule isnocL $e (Cons $h $tl) ↪ Cons $h (isnocL $e $tl);

// rev: reverse a list
symbol revL [A : Set] : τ (ilistS A) → τ (ilistS A);
rule revL Nil ↪ Nil;
rule revL (Cons $h $tl) ↪ isnocL $h (revL $tl);

// length: length of a list
symbol lengthL [A : Set] : τ (ilistS A) → τ N;
rule lengthL Nil ↪ zero;
rule lengthL (Cons _ $tl) ↪ succ (lengthL $tl);

// Proofs

// Left identity of app : Nil on the left is a neutral element for app.
symbol appL_nil_l [A : Set] (l : τ (ilistS A)) : π (appL Nil l = l) ≔
begin
    reflexivity
end;

// Right identity of app : Nil on the right is a neutral element for app.
symbol appL_nil_r [A : Set] (l : τ (ilistS A)) : π (appL l Nil = l) ≔
begin
    assume A l;
    refine ind_ilist A (λ w, appL w Nil = w) _ _ l
    {
        reflexivity
    }
    {
        assume h tl ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;

// Associativity of app
symbol appL_assoc [A : Set] (l1 : τ (ilistS A)) (l2 : τ (ilistS A)) (l3 : τ (ilistS A)) :
π (appL (appL l1 l2) l3  =  appL l1 (appL l2 l3)) ≔
begin
    assume A l1 l2 l3;
    refine ind_ilist A (λ w, appL (appL w l2) l3 = appL w (appL l2 l3)) _ _ l1
    {
        simplify;
        reflexivity
    }
    {
        assume h tl ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;

// isnoc distributes over app : appending l1 & l2 then adding at the end of the l2
// is the same thing as adding at the end of l2 first then appending it to l1.
symbol isnocL_appL [A : Set] (e : τ A) (l1 l2 : τ (ilistS A)) :
    π (isnocL e (appL l1 l2) = appL l1 (isnocL e l2)) ≔
begin
    assume A e l1 l2;
    refine ind_ilist A (λ w, isnocL e (appL w l2) = appL w (isnocL e l2)) _ _ l1
    {
        simplify;
        reflexivity
    }
    {
        assume h tl ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;
// isnoc can be rewritten with app:
// adding e at the end of l is the same thing as
// appending the singleton list [e].
symbol isnocL_as_appL [A : Set] (e : τ A) (l : τ (ilistS A)) :
    π (isnocL e l = appL l (Cons e Nil)) ≔
begin
    assume A e l;
    refine ind_ilist A (λ w, isnocL e w = appL w (Cons e Nil)) _ _ l
    {
        simplify;
        reflexivity
    }
    {
        assume h td ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;

// rev distributes over app while conserving the order :
// reversing a concatenation reverses each part and swaps their order
symbol revL_appL [A : Set] (l1 : τ (ilistS A)) (l2 : τ (ilistS A)) : π (revL (appL l1 l2) = appL (revL l2) (revL l1) ) ≔
begin
    assume A l1 l2;
    refine ind_ilist A (λ w, revL (appL w l2) = appL (revL l2) (revL w)) _ _ l1
    {
        simplify;
        rewrite appL_nil_r;
        reflexivity
    }
    {
        assume h tl ih;
        simplify;
        rewrite ih;
        rewrite isnocL_appL;
        reflexivity
    }
end;

//reversing a list twice gives back the original list
symbol revL_revL [A : Set] (l : τ (ilistS A)) : π (revL (revL l) = l) ≔
begin
    assume A l;
    refine ind_ilist A (λ w, revL (revL w) = w) _ _ l
    {
        simplify;
        reflexivity
    }
    {
        assume h tl ih;
        simplify;
        rewrite isnocL_as_appL;
        rewrite revL_appL;
        rewrite ih;
        simplify;
        reflexivity
    }
end;

// The length of a concatenation is the sum of the lengths.
symbol lengthL_appL [A : Set] (l1 : τ (ilistS A)) (l2 : τ (ilistS A)) : π (lengthL (appL l1 l2 ) = (lengthL l1 + lengthL l2)) ≔
begin
    assume A l1 l2;
    refine ind_ilist A (λ w, lengthL (appL w l2) = (lengthL w + lengthL l2)) _ _ l1
    {
        simplify;
        reflexivity
    }
    {
        assume h tl ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;