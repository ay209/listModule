// N with ind_N, the order <, and addition with its five rules.
require open Stdlib.Prop;
require open Stdlib.Set;
require open Stdlib.Eq;

constant symbol N : Set;
constant symbol zero : τ N;
constant symbol succ : τ N → τ N;

symbol ind_N : Π p : τ N → Prop,
               π (p zero) →
               (Π n : τ N, π (p n) → π (p (succ n))) →
               Π n : τ N, π (p n);

rule ind_N $p $base $step zero ↪ $base;
rule ind_N $p $base $step (succ $n) ↪ $step $n (ind_N $p $base $step $n);

symbol + : τ N → τ N → τ N;
notation + infix left 6;

symbol < : τ N → τ N → Prop;
notation < infix 4;

rule zero < succ $y ↪ ⊤;
rule succ $x < succ $y ↪ ($x < $y);
rule $x < zero ↪ ⊥;

rule zero + $y ↪ $y;
rule succ $x + $y ↪ succ ($x + $y);
rule $x + zero ↪ $x;
rule $y + succ $x ↪ succ ($y + $x);

assert n m ⊢ succ (n + m) ≡ n + succ m;
rule ($x + $y) + $z ↪ $x + ($y + $z);
//rule $x + $y ↪ $y + $x;
assert n m k ⊢ (n + m) + k ≡ n + (m + k);
assert n ⊢ ((n + n) + n) + n ≡ n + (n + (n + n));
assert n m k ⊢ succ ((n + m) + k) ≡ (n + succ m) + k;

symbol test1 : π (zero < succ zero) ≔
begin
    simplify;
    apply ⊤ᵢ;
end;
symbol test2 : π (¬ (zero < zero)) ≔
begin
    simplify;
    assume p;
    apply p;
end;
symbol plus_assoc [n m k : τ N] : π (((n + m) + k) = (n + (m + k))) ≔
begin
    assume n m k;
    refine ind_N (λ w, ((w + m) + k) = (w + (m + k))) _ _ n
    {
        simplify;
        reflexivity
    }
    {
        assume n0 ih;
        simplify;
        reflexivity
        
    }
end;


symbol succ_plus [n m : τ N] : π ((succ (n + m)) = (n + (succ m))) ≔
begin
    assume n m;
    refine ind_N (λ w, (succ (w + m)) = (w + (succ m))) _ _ n
    {
        simplify;
        reflexivity
    }
    {
        assume n0 ih;
        simplify;
        rewrite ih;
        reflexivity
    }
end;
symbol plus_comm [n m : τ N] : π ((n + m) = (m + n)) ≔
begin
    assume n m;
    refine ind_N (λ w, (w + m) = (m + w)) _ _ n
    {
        simplify;
        reflexivity
    }
    {
        assume n0 ih;
        simplify;
        rewrite ih;
        reflexivity
        
    }
end;
/*
inductive even : τ N → TYPE ≔
| EZero : even zero
| ESuccSucc : even succ zero → even (succ (succ (zero)));
*/
inductive tagged : τ N → TYPE ≔
| Tag : Π m : τ N, tagged m;