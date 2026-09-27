// vecV2.lp
// Adds elements of type A. Compared to the first version, A is an index
// of the type, so it must be written explicitly in every constructor
// (VNil A, VCons A n h tl).
// Contents: app, rev, map, length; lemmas app_nil_r and app_nil_l.

require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Eq;
require open listModule.nat;


inductive vec : Set → τ N → TYPE ≔
| VNil : Π A : Set, vec A zero
| VCons : Π A : Set, Π n : τ N, τ A → vec A n → vec A (succ n);

print ind_vec;

constant symbol vecS : Set → τ N → Set;
rule τ (vecS $A $n) ↪ vec $A $n;

symbol app [A : Set] [n m : τ N] : vec A n → vec A m → vec A (n + m);

rule app (VNil $A) $l ↪ $l;
rule app (VCons $A $n $h $tl) $l ↪ VCons $A _ $h (app $tl $l);

symbol rev [A : Set] [n : τ N] : vec A n → vec A n;

rule rev (VNil $A) ↪ VNil $A;
rule rev (VCons $A $n $h $tl) ↪ app (rev $tl) (VCons $A zero $h (VNil $A));


// map5: apply f to every element, preserving length.
symbol map [A B : Set] [n : τ N] : (τ A → τ B) → vec A n → vec B n;

rule map _ (VNil $A) ↪ VNil _;
rule map $f (VCons $A $n $h $tl) ↪ VCons _ _ ($f $h) (map $f $tl);

// lengthV5: direct projection of the length index.
symbol length [A : Set] [n : τ N] (v : vec A n) : τ N ≔ n;
// Proofs


symbol app_nil_r [A : Set] [n : τ N] (v : τ (vecS A n)) : π (app v (VNil A) = v) ≔
begin
    assume A n v;
    refine ind_vec (λ a p w, app w (VNil a) = w) _ _ A n v
    {
        simplify;
        reflexivity
    }
    {
        assume x0 x2 x3 x4 ih;
        simplify;
        rewrite ih;
        reflexivity

    }
end;

symbol app_nil_l [A : Set] [n : τ N] (v : τ (vecS A n)) : π (app (VNil A) v = v) ≔
begin
    assume A n v;
    refine ind_vec (λ a p w, app (VNil a) w = w) _ _ A n v
    {
        simplify;
        reflexivity
    }
    {
        assume x0 x2 x3 x4 ih;
        simplify;
        reflexivity
    }
end;


// kept for demonstration
// the full proof is in vecV3.lp (appV_assoc).
/*
symbol app_assoc [A : Set] [n m k : τ N] (v1 : τ (vecS A n)) (v2 : τ (vecS A m)) (v3 : τ (vecS A k)) :
    π ((app (app v1 v2) v3) = (app v1 (app v2 v3))) ≔
begin
    assume A n m k v1 v2 v3;
    refine ind_vec (λ a p w, (app (app w v2) v3) = (app w (app v2 v3))) _ _ A n v1
    {
        // base case
    }
    {
        // inductive case
    }
end;*/