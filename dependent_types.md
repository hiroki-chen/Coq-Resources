# Dependent Types

When we discuss some predicate in type theory, we are actually using the type $P$ from a universe $\cal U$ where $P$ becomes a term in the universe, or inhabitant. As its name, a dependent type means type dependent on a term, written $P(a): \cal U$ where $a$ is a term of $A$, meaning that the type $P(a)$ is dependent on $a:A$. Formally, $\Gamma, x: A \vdash P(x) : \cal U$.

Do note that $P(x)$ is not a function! If so, the type should be $A \to \mathcal{U}: \mathcal{U}$ which is self-contradictory: recall the Russels’ paradox. A set cannot contain itself (**Impredicativity**). A predicate with self-referential elements is impossible to deal with. The workaround is the introduction of hierarchy of the universe, which creates high-order logic systems. The thing is that we *cannot* have a sets of *all* sets; there are always “larger” sets.

Dependent types are useful in the context of computer-aided proofs. This is because if $\Gamma, x: A \vdash P(x) : \cal U$, we can derive some lovely properties for $x$ since types are predicates. This somehow reflects the first-order logic: we fix something $x$ and want to reason some propositions/theorems/lemmas on it. For example, we say if $n \in \mathbb{N}$ then $\mathrm{odd}(n) \vee \mathrm{even}(n)$. In this deduction, we indeed yet implicitly constructed a new type by $\Gamma, n : \mathbb{N} \vdash \mathrm{odd}(n) + \mathrm{even}(n) : \cal U.$

## Polymorphism? Dependent type?

One might be confused with polymorphism when it comes to dependent type as they seem to be a similar notion.

- Polymorphism: It allows entities to be treated as instances of a **more generic type rather than their specific type.** → It is interested in different types. Parameterized by type universe.

```coq
Inductive my_list (a: Set): Set := ...
(* or *)
Inductive my_list': Set -> Set := ...
(* or *)
Inductive my_list'': forall (a: Set), Set := ...

Check my_list.
Check my_list'.
Check my_list''.
------------------
my_list*: Set -> Set.
```

- Dependent type: It allows types to be parameterized **by a term of a fixed type**. → It is interested in different instances of a type. We can write in the following forms: Parameterized by a type.

```coq
Inductive my_list (n: nat): Set := ...
(* or *)
Inductive my_list': nat -> Set := ...
(* or *)
Inductive my_list'': forall _: nat, Set := ...

Check my_list.
Check my_list'.
Check my_list''.
------------------
my_list*: nat -> Set.
```

P.S.: Coq's forall is a dependent product type $\Pi_{a: Type} a \rightarrow \cal U$; You can think of the arrow as just syntactic sugar:

```coq
A -> B <==> forall _: A, B
```

## Doing dependent types in Coq

Typically there are two means of defining dependent types. The first choice is to define them as *inductive types* while the other one is to define *functions* that work on types.

```coq
Inductive Vec {A: Set}: nat -> Set :=
  | nil: Vec O
  | cons: forall n, A -> Vec n -> Vec (S n)
.
```

```coq
Fixpoint Vec {A: Set} (n: nat): Set :=
  match n with
  | O => unit
  | S n' => A * Vec n'
  end.
```

As per [this thread](https://proofassistants.stackexchange.com/questions/2708/comparing-indexed-induction-to-recursion/2709#2709) on proof assistant stack exchange, these two styles should be carefully chosen. In most cases, the indexed inductive type would be a greater option because it allows:

* Fast syntactical pattern match.
* Easy inductive cases where you cannot analyze with `Fixpoint`s.
* Hiding all the constructors.
* Complex data structures that can be expressed in a GADT fasion (like a program's syntax).

## Doing `Inversion` in Coq

One annoying thing about dependent types is that doing `inversion` on the witness of equality can be non-trivial and somehow difficult to understand. As an example, let us consider again the inductively defined vector type `Vec`.

```coq
Inductive Vec {A: Set}: nat -> Set :=
  | nil: Vec O
  | cons: forall n, A -> Vec n -> Vec (S n)
.

Inductive foo: forall n, @Vec nat n -> Prop :=
  | trivial_case: forall v, foo 0 v
  | other_case: forall n n' v v', S n' = n -> foo n' v' -> foo n v
.

Theorem bar: forall n (v1 v2: Vec n), foo n v1 -> foo n v2 -> v1 = v2.
Proof.
  intros.
  inversion H.
```

What happens when we perform `inversion H`? It produces something very weird:

```coq
n ℕ 
v1v2 Vec n 
H foo n v1 
H0 foo n v2 
v Vec 0 
H1H3 0 = n 
H4 existT (λ x : ℕ ⇒ Vec x) 0 v = existT (λ x : ℕ ⇒ Vec x) n v1 
=========================
Goal is  v1 = v2
```

Now we have `H4: existT (λ x : ℕ ⇒ Vec x) 0 v = existT (λ x : ℕ ⇒ Vec x) n v1`. What is this `existT` thing? To understand this, we may need to delve into Coq's standard library `Coq.Init.Specif` which defines $\Sigma$ types (also known as dependent pair types). 

> `(sig A P)`, or more suggestively `{x:A | P x}`, denotes the subset of elements of the type `A` which satisfy the predicate `P`. Similarly `(sig2 A P Q)`, or `{x:A | P x & Q x}`, denotes the subset of elements of the type `A` which satisfy both `P` and `Q`.

This `sigT`  type is just a syntax sugar for `{x: A & (P x)}` which is a sigma type that incorporates the existential quantifier.

```coq
#[universes(template)]
Inductive sigT (A:Type) (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.
```

So `existT` is just the constructor for the dependent pair type that generally hides the detail behind the index `A` inhabitated by `x`. For dependent types, it is trivial to believe that if `n1 = n2` then we know that at type level, `Vec n1 = Vec n2`; but this is not the other way around. The implication of the other direction is deeply rooted in a classical question: is identity proof *unique*?

Fortunately it has been proved that if equality over type $A$ on which the dependent type depend is *decidable* then there the identity type is unique and inhabitated only by `refl`.

```coq
Lemma UIP: forall (x y: U) (p1 p2: x = y), p1 = p2.
Lemma UIP_refl : forall (x:U) (p: x = x), p = eq_refl x.
```

## Streicher's K Axiom and Extensional Type Theory

Let us not talk about HoTT for now (although it explicitly gives us a more reasonable view for identities over identities). Now we focus on dependent types in MLTT. We often write identity types, or prositional equality as `x = y` or $\mathsf{Id}(x, y)$. This type is only constructable via `refl: A -> A -> Prop`. The proof to that type is that $x$ is (by "is" I mean they are identical syntactically, not "semantically") $y$.

Unfortunately, in naive MLTT, there is no way to reason about equality over dependent types. This is why K axiom comes into play. It generally states that each term of each identity type is *propositionally equal* to the caconical reflexivity equality proof `refl: Id_A(x,x)`:

$$
  K: \prod_{A: \mathcal{U}}\prod_{x: A}\prod_{P: Id_A(x,x) \to \mathcal{U}}\left (P(\mathsf{refl}_Ax) \to \prod_{h: \mathsf{Id}_A(x,x)} P(h)\right).
$$

```coq
Lemma Streicher_K :
  forall {A: Type} (x: A) (P: x = x -> Prop), P (eq_refl x) -> forall h: x = x, P h.
```

If we take some deeper look at HoTT, we know that identity types are just continuous path from a point to another point in some space $A$ (a type). Chances are paths are not the same because canonical equality implies a loop over the point whereas propositional equality can of course be a non-trivial "path". Do two paths always agree? Not necessarily. There is thus a need to reason about higher groupoid structure of types. In MLTT, the higher groupoid structure is kind of boring because everything can only be `refl`. K Axiom, however, is incompatible with *univalence axiom*.

$$
  (A \simeq B) \simeq (A = B).
$$

The reason for this is simple, as K's axiom forces all evidence for `a = b` to be `refl`, which is not the case when it comes to HoTT and if the set is not decidable w.r.t. equality. K is nevertheless required for dependent pattern matching if we adhere to MLTT. This is why we will need this:

```coq
Definition do_match n (v: @Vec Nat n) :=
  match n as n' in n = n' -> ... with
  | ... => ...
  | ... => ...
  ...
  end eq_refl.
```

Since we know `K: (p: x = x) -> p = refl` then we have `K refl = refl`.

AFAIK, Agda is able to disable K in the proof mode.
