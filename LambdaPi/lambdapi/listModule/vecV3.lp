// vecV3.lp
// Final version of an indexed list, where a is passed as a parameter,
// so that it is implicit in the constructors (VNil, VCons h n tl).
// Contents: appV, revV, isnocV, zipV, mapV, nthV (which requires a proof
// that the index is in bounds); lemmas appV_assoc and isnocV_app.

require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Eq;
require open listModule.nat;

(a:Set) inductive V : τ N → TYPE ≔
| VNil : V a zero
| VCons : τ a → Π n : τ N, V a n → V a (succ n);

print ind_V;

constant symbol VS : Set → τ N → Set;
rule τ (VS $a $n) ↪ V $a $n;

constant symbol x : Set → Set → Set;
notation x infix right 10;

symbol < : τ N → τ N → Prop;
notation < infix 4;

rule zero < succ $y ↪ ⊤;
rule succ $x < succ $y ↪ ($x < $y);
rule $x < zero ↪ ⊥;

(A : Set) (B : Set) inductive prod : TYPE ≔
| pair : τ A → τ B → prod A B;

rule τ ($A x $B) ↪ prod $A $B;

symbol fst [A B : Set] : τ (A x B) → τ A;

rule fst (pair $a _) ↪ $a;

symbol snd [A B : Set] : τ (A x B) → τ B;

rule snd (pair _ $b) ↪ $b;

// Functions

symbol appV [a : Set] [n m : τ N] : V a n → V a m → V a (n + m);

rule appV VNil $l ↪ $l;
rule appV (VCons $h $n $tl) $l ↪ VCons $h _ (appV $tl $l);

symbol revV [a : Set] [n : τ N] : τ (VS a n) → τ (VS a n);

rule revV VNil ↪ VNil;
rule revV (VCons $h $n $tl) ↪ appV (revV $tl) (VCons $h zero VNil);

symbol isnocV [a : Set] [n : τ N] : τ a → τ (VS a n) → τ (VS a (succ n));

rule isnocV $e VNil ↪ VCons $e zero VNil;
rule isnocV $e (VCons $h $n0 $tl) ↪ VCons $h _ (isnocV $e $tl);

symbol zipV [a b : Set] [n : τ N] : τ (VS a n) → τ (VS b n) → τ (VS (a x b) n);

rule zipV VNil VNil ↪ VNil;
rule zipV (VCons $h1 $n0 $tl1) (VCons $h2 _ $tl2) ↪ VCons (pair $h1 $h2) _ (zipV $tl1 $tl2);

symbol mapV [a b : Set] [n : τ N] : (τ a → τ b) → τ (VS a n) → τ (VS b n);

rule mapV _ VNil ↪ VNil;
rule mapV $f (VCons $h $n0 $tl) ↪ VCons ($f $h) _ (mapV $f $tl);

symbol nthV [a : Set] [n : τ N] (i : τ N) (h : π (i < n)) : τ (VS a n) → τ a;

rule nthV zero $h (VCons $head _ _) ↪ $head;
rule nthV (succ $i) $h (VCons _ $n0 $tl) ↪ nthV $i $h $tl;

// Lemmas

symbol appV_assoc [a : Set] [n m k : τ N] (v1 :τ (VS a n)) (v2 : τ( VS a m)) (v3 : τ (VS a k)) :
    π ((appV (appV v1 v2) v3) = (appV v1 (appV v2 v3))) ≔
begin
    assume a n m k v1 v2 v3;
    refine ind_V a (λ p w, (appV (appV w v2) v3) = (appV w (appV v2 v3))) _ _ n v1
    {
        simplify;
        reflexivity
    }
    {
        assume x0 x2 x3 ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;



//     Commutativity cannot be added as a
//     rewrite rule, because it would not terminate.
/*
symbol revV_app [a : Set] [n m : τ N] (v1 : τ (VS a n)) (v2 : τ (VS a m)) :
    π ((revV (appV v1 v2)) = (appV (revV v2) (revV v1))) ≔
begin
    assume a n m v1 v2;
    refine ind_V a (λ p w, (revV (appV w v2)) = (appV (revV v2) (revV w))) _ _ n v1
    {
        // base case
    }
    {
        // inductive case
    }
end;*/

symbol isnocV_app [a : Set] [n m : τ N] (e : τ a) (v1 : τ (VS a n)) (v2 : τ (VS a m)) :
    π ((isnocV e (appV v1 v2)) = (appV v1 (isnocV e v2))) ≔
begin
    assume a n m e v1 v2;
    refine ind_V a (λ p w, (isnocV e (appV w v2)) = (appV w (isnocV e v2))) _ _ n v1
    {
        simplify;
        reflexivity
    }
    {
        assume h n0 v0 ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;
//   - nthV_test: relates nthV and mapV; unfinished, 
// the induction would need to generalize over the index and its bound proof.
/*
symbol nthV_test [a b : Set] [n : τ N] (f : τ a → τ b) (i : τ N) (h : π (i < n)) (v1 : τ (VS a n)) :
    π (nthV i h (mapV f v1) = f (nthV i h v1)) ≔
begin
    assume a b n f i h v1;
    refine ind_V a (λ r w, nthV i h (mapV f w) = f (nthV i h w)) _ _ n v1
    {
       
    }
    {
        
    }
end;*/
