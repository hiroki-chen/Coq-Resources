# Proof Irrevelance

Have you ever wondered when we talking a proposition $P$'s proof $p$, do we really care *the detail of the proof*, or do we just care about that $P$ is *provable*?

From the perspective of type theory, we know that programs are just proofs for some propositions thanks to Curry-Howard Correspondence, and sometimes we will make some premise on some programs. A most common use case for this is extracting the $n$-th element from the list.

```coq
Definition extract {A: Set} (l: list A) (n: nat): n < length l -> A.
```

The above definition says we can only construct a valid type $a: A$ which is the $n$-th element of $l$ given that $n$ is smaller than the length of the list. Now, let us assume that we have two elements:

```
a1 := extract l 10 proof1
a2 := extract l 10 proof2
```

The proofs are derived in a different fashion with the same type, but are you confident enough to say that $a_1 = a_2$? A classical result of type theory says that equalities between elements of a type are proof irrelevant if $T$ has decidable equality. Thus, if $A$ in the above case is decidable, then we are confident that $a1 = a2$ holds propositionally.

```coq
Fail Definition irrelevance x (p : x = x) : p = eq_refl x :=
  match p in _ = y return p = eq_refl x with
  | eq_refl => eq_refl
  end.
```

This would fail because we have to generalize $p$ with its index in the `in` clause to something like $x = y$; and Coq does not belive that $x = y$ is propositionally equal to `eq_refl`.

But why decidable equality makes Coq happy to reason about all proofs are the same?

```coq
Variable T : Type.
Implicit Types x y : T.
Hypothesis eq_dec: forall x y, x = y \/ x <> y.

Definition normalize {x y} (p : x = y) : x = y :=
  match eq_dec x y with
  | or_introl e => e
  | or_intror _ => p
  end.
```

We use decidable equality to define a normalization procedure that takes a proof of equality as input and produces a canonical proof of equality of the same type as output. One should be aware that this function actually always produces the constant result because the other branch is contradictory. 

```coq
Lemma normalize_const {x y} (p q : x = y) : normalize p = normalize q.
Proof. by rewrite /normalize; case: (eq_dec x y). Qed.
```