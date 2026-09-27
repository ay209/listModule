// vecV1.lp
// Simplest version of an indexed list: vectors carry only their length
// and contain no elements.
// Contents: type vec, concatenation app, associativity lemma app3_assoc.
require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Eq;
require open listModule.nat;

inductive vec : τ N → TYPE ≔
| VNil : vec zero
| VCons : Π n : τ N, vec n → vec (succ n);

print ind_vec;

constant symbol vecS : τ N → Set;
rule τ (vecS $n) ↪ vec $n;


symbol app [n m : τ N] : τ (vecS n) → τ (vecS m) → τ (vecS (n + m));

rule app VNil $l ↪ $l;
rule app (VCons $n $tl) $l ↪ VCons _ (app $tl $l);

symbol app3_assoc [n m k : τ N] (v1 : τ (vecS n)) (v2 : τ (vecS m)) (v3 : τ (vecS k)) :
    π ((app (app v1 v2) v3) = (app v1 (app v2 v3))) ≔
begin
    assume n m k v1 v2 v3;
    refine ind_vec (λ p w, (app (app w v2) v3) = (app w (app v2 v3))) _ _ n v1
    {
        simplify;
        reflexivity
    }
    {
        assume x0 x2 ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;