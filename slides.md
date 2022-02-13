---
theme: apple-basic
class: text-center
highlighter: prism
lineNumbers: false
drawings:
  persist: false
---

<h1>Software can literally<br>be perfect</h1>

<h2>How Formal Verification and Magmide<br>could make provably correct code<br>tractable for practicing software engineers.</h2>

<style>
.slidev-layout {
  @apply px-[4rem] py-[8rem];
}
.slidev-layout h1 {
  @apply text-5xl mb-[4rem];
}
</style>

---

# Formal Verification

<v-clicks>

- What is it?
- Core ideas
- Magmide
- Prerequisites: type systems, especially Rust

</v-clicks>

---

# Software is broken

- Security breaches
- Ransomware attacks
- Operational failures
- Safety critical failures

---

# Software is broken

<v-click>

<br>

## *Consortium for Information & Software Quality*
## [The Cost of Poor Software Quality in the US: A 2020 Report](https://www.it-cisq.org/pdf/CPSQ-2020-report.pdf)

- $1.56 trillion in operational failures
- $1.31 trillion in technical debt

</v-click>

<v-click>

## *McAfee*
## [The Hidden Costs of Cybercrime](https://www.mcafee.com/enterprise/en-us/assets/reports/rp-hidden-costs-of-cybercrime.pdf)

- $945 billion monetary loss from cybercrime in 2020
- $145 billion global spending on cybersecurity in 2020
- up from $522.5 billion in 2018

</v-click>

<style>
.slidev-layout {
  @apply px-[10rem] py-[3rem] text-lg;
}
</style>

---

# Software is broken

- Software underpins critical social infrastructure.
- Broken software hurts people.
- Broken software slows down human progress.

---

# It doesn't have to be this way!

- Software is just information that represents pure logic.
- Relies on hardware assumptions, but can itself be literally mathematically perfect.
- Provably correct code is possible with formal verification.

---

## [Quanta Magazine: Hacker-Proof Code Confirmed](https://www.quantamagazine.org/formal-verification-creates-hacker-proof-code-20160920/)

<br>

<img class="h-[20vh]" src="https://d2r55xnwy6nx47.cloudfront.net/uploads/2016/09/ProgramVerification_BoyaSun_2K.jpg" />

<v-clicks>

- DARPA funded team.
- Quadcopter control software.
- Red team of world-class hackers.
- Logical proof of security.
- Tools are purpose-built, not very usable elsewhere.

</v-clicks>

<style>
.slidev-layout {
  @apply px-[12rem] py-[4rem] text-lg;
}
</style>

---

# Magmide

- Bring formal verification out of the ivory tower to practicing engineers.
- Proof language as a verified bare metal program.
- Foundation for verified programs for any architecture or environment.

<v-click>

## Is this possible?

</v-click>

<v-click>

- Understanding makes it easier to believe.

</v-click>

---

# Core concepts of formal verification

- Dependent Types
- Type Checking is Proof Checking
- Separation Logic

---

# Dependent Types

- More powerful than normal types.

---

```rust
fn is_one(n: u64) -> bool {
  n == 1
}
```

<v-click>

`(u64) -> bool`

</v-click>

<style>
.slidev-layout {
  @apply text-3xl;
}
</style>

---

Same type as `is_one`, very different behaviors.

```rust
fn is_zero(n: u64) -> bool {
  n == 0
}
fn always_true(_: u64) -> bool {
  true
}
fn always_false(_: u64) -> bool {
  false
}
// ... many other possible functions
```

<v-click>

- Testing can only guarantee correctness with small finite functions.
- Real guarantees need the type system.

</v-click>

<style>
.slidev-layout {
  @apply py-[2rem] text-xl;
}
</style>

---

# Dependent Types

<v-clicks>

- Normal types can only reference other types.
- Dependent types can reference *values*.

</v-clicks>

---

# Dependent Types (using Coq)

```v
Program Definition is_one n: {b | b = true <-> n = 1} :=
  match n with
  | 1 => true
  | _ => false
  end.
Solve All Obligations with (simpl; lia).
```

<v-click>

`forall (n: nat), {b: bool | b = true <-> n = 1}`

</v-click>

<v-click>

<br>

Coq makes this painful, but it's possible!

</v-click>

---

# Type Checking is Proof Checking

```v {3,7}
Program Definition is_one n: {b | b = true <-> n = 1} :=
  match n with
  | 0 => true // <- mistake!
  | _ => false
  end.
Solve All Obligations with (simpl; lia).
// ❌ unable to unify!
```

<v-clicks>

- The *type system* checks that everything is consistent.
- All type systems represent some logic.
- Checking type safety like finding a proof.

</v-clicks>

---

```v
Inductive Even: nat -> Prop :=
  | Even_0: Even 0
  | Even_plus_2: forall n, Even n -> Even (S (S n)).
```

<v-clicks>

- `Even` takes `nat` and gives logical proposition.
- `Even_0` has *type* declaring `0` is even.
- `Even_plus_2` has *type* that if any `n` is even, so is `n + 2`

</v-clicks>

---

```v
Inductive Even: nat -> Prop :=
  | Even_0: Even 0
  | Even_plus_2: forall n, Even n -> Even (S (S n)).
```

Coq is lisp-like, not C-like.

<v-clicks>

- `(foo a b)` rather than `foo(a, b)`.
- `(S (S n))` same as `n + 1 + 1`.

</v-clicks>

---

```v
Inductive Even: nat -> Prop :=
  | Even_0: Even 0
  | Even_plus_2: forall n, Even n -> Even (S (S n)).
```

```v
Definition four_is_even: Even 4.
Proof.
  repeat constructor.
Qed.
```

<v-click>

```v
Definition four_is_even_manual: Even 4 :=
  (Even_plus_2 2 (Even_plus_2 0 Even_0)).
```

</v-click>

---

```v
Fixpoint double (n: nat) :=
  match n with
  | O => O
  | S sub_n => S (S (double sub_n))
  end.
```

<v-click>

```v
Definition even_double: forall n, Even (double n).
Proof.
  induction n; constructor; assumption.
Qed.
```

</v-click>

<v-clicks>

- `even_double` is a *proof* transforming function.
- `even_double` is *literally infinitely* better than a unit test.
- Didn't have to change definition of `double`.

</v-clicks>

<style>
.slidev-layout {
  @apply py-[3rem];
}
</style>

---

# If you want to learn more:

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/)
- and many others...

---

Dependently typed proof languages are extremely powerful:

- [Feit–Thompson theorem](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem)
- [DeepSpec](https://deepspec.org/main)
- [HACMS: High Assurance Cyber Military Systems](https://loonwerks.com/projects/hacms.html)
- [Project Everest](https://project-everest.github.io/)

---

# Why isn't everyone doing this?

<v-clicks>

- Research Debt
- Pure Functional Dogma

</v-clicks>

---

# [Research Debt](https://distill.pub/2017/research-debt/) - Chris Olah, Shan Carter

> There's a tradeoff between the energy put into explaining an idea, and the energy needed to understand it. On one extreme, the explainer can painstakingly craft a beautiful explanation, leading their audience to understanding without even realizing it could have been difficult. On the other extreme, the explainer can do the absolute minimum and abandon their audience to struggle. This energy is called interpretive labor.

<v-click at="1">

> People expect the climb to be hard. It reflects the tremendous progress and cumulative effort that's gone into mathematics. The climb is seen as an intellectual pilgrimage, the labor a rite of passage. But the climb could be massively easier. It's entirely possible to build paths and staircases into these mountains. The climb isn't something to be proud of.

> The climb isn't progress: the climb is a mountain of debt.

</v-click>

<v-click at="2">

> The insidious thing about research debt is that it's normal. Everyone takes it for granted, and doesn't realize that things could be different.

</v-click>

<v-click at="3">

Academia has bad incentives to<br>
properly explain and expose their work.

</v-click>

<style>
.slidev-layout {
  @apply px-[6rem] pt-[4rem] pb-[5rem];
}
</style>

---

# Pure Functional Dogma

<v-clicks>

- No mutation or side effects.
- But it's always a lie!
- Computers are just big chunks of mutable state.
- Have to reason about real computation.

</v-clicks>

---

# Separation Logic

- Logical framework for reasoning about mutable state.
- Surprisingly uncommon.

---

# ... Normal Logic

```
P ∧ Q
```

<v-click>

<br>

```
P ∧ Q
equivalent to:
(P ∧ Q) ∧ P
```

</v-click>

---

Perfectly reasonable for pure facts.

<br>

```
Even(4) ∧ (1 + 1 = 2)
equivalent to:
(Even(4) ∧ (1 + 1 = 2)) ∧ Even(4)
```

---

What about mutable facts?

```
a --> 1
```

<v-click>

<br>

memory location `a` points to `1`

</v-click>

---

`// {program assertions}`

```rust
// {a --> 1}
let a_value = *a;
// {a --> 1}
assert(a_value == 1);
// {a --> 1}
```

<v-click>

```rust
// {a --> 1}
some_function(a);
// {a --> 1 ∧ a --> ???}
let a_value = *a;
assert(a_value == 1); // ❌
```

</v-click>

<v-click>

<br>

```
(a --> 1) ∧ (a --> 2)
```

</v-click>

<style>
.slidev-layout {
  @apply py-[2rem];
}
</style>

---

# Normal Logic

- `∧` operator too lenient for mutable facts.
- Difficult to scale program reasoning.
- Had to reason about entire program rather than composable pieces.

---

# Separation Logic

```
// Not Allowed! ❌
(a --> 1) * (a --> 1)
```

<v-clicks>

- pronounced "and separately"
- called separating conjunction
- requires state assertions to be disjoint, separate
- doesn't allow duplicating assertions

</v-clicks>

<v-click>

<br>

```
// Okay! ✅
(a --> 1) * (b --> 2)
```

</v-click>

---

```rust
// {a --> 1}
let a_value = *a;
assert(a_value == 1);
// {a --> 1}
some_function(a);
// {}
// let a_value = *a;
// ❌ no longer own a!
```

<v-clicks>

- Must give away ownership.
- Allows small-scale composable proofs.
- Directly inspired Rust.
- More concepts, can be more complex.

</v-clicks>

<style>
.slidev-layout {
  @apply py-[3rem];
}
</style>

---

# Rust Borrow Checker

<v-clicks>

- Represents a *decidable subset* of a fractional separation logic.
- Like a "proof finder", sometimes called a certified decision procedure.
- Can always determine correctness of safe Rust.
- Can't figure out correctness of `unsafe` code.
- Rust needs `unsafe` to actually be realistic and useful.

</v-clicks>

<style>
.slidev-layout {
  @apply py-[3rem];
}
</style>

---

# Iris Separation Logic

<v-clicks>

- Built to verify arbitrarily complex Rust programs.
- Written in Coq. Researchers write proofs rather than relying on a decidable algorithm.
- [Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)
- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)
- Type system, ownership and lifetimes, `Send` and `Sync`.
- `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex`, `RwLock`, `mem::swap`, `thread::spawn`, `rayon::join`, `take_mut`
- Iris/Iron powerful enough to verify no resource leaks!

</v-clicks>

<style>
.slidev-layout {
  @apply py-[3rem] text-xl;
}
</style>

---

# Why isn't everyone using Iris?

<v-clicks>

- Research debt.
- Not a directly usable language.
- Only built for "on the side" proofs.

</v-clicks>

<br>

<v-click>

```
funrec option_as_mut(x) ret ret :=
  let r = new(2) in
  letcont k() := delete(1, x); jump ret(r) in
  let y = ∗x in case ∗y of
  − r :=={inj 0} (); jump k()
  − r :=={inj 1} y.1; jump k()
```

</v-click>

---

# Magmide

Necessities to achieve goal:

- Fully verifiable
- Capable of bare metal performance
- Gradually verifiable
- Fully reusable
- Practical and usable
- Taught effectively

---

# Fully verifiable

- Max out logical power with full type theory.
- Able to formalize any assertion.
- Decidable subsets still possible.
- Don't always have to use full power.

---

# Capable of bare metal performance

- Max out computational power, use Iris.
- LLVM-like abstract assembly language, hardware axioms at bottom.
- Less performant abstractions still possible.

<img class="pt-1 h-[36vh] mx-auto" src="https://camo.githubusercontent.com/4d0e55295556938fca5efa11c4f57d902f2c615d82c0ff90071e761f8872cd67/68747470733a2f2f692e737461636b2e696d6775722e636f6d2f39784744652e706e67" />

<style>
.slidev-layout {
  @apply py-[3rem] text-lg;
}
</style>

---

# Gradually verifiable

- Trackable effects.
- Knowledge of program safety is absolute but flexible.
- Incremental adoption and realistic iteration.
- Converge toward correctness.

---

# Fully reusable

- Verification pyramid.
- Foundations pass on provably safe abstractions.
- Metaprogramming and query-based compiler.
- Higher level languages can "lift" full power, have escape hatches, use Magmide functions.
- Don't have to write proofs for everything.

---

# Practical and usable

- Rust/Cargo prove we can have nice things.
- Remove incidental complexity, focus essential complexity.

---

# Taught effectively

- Respect user's time.
- Formal verification is learnable.
- Assume reader is trying to get something done.
- Concrete examples before formal definitions.
- Call out true prerequisites.
- Use graspable words not opaque and unsearchable non-ascii symbols.
- Syntax should make it easy to find definitions.

---

# Magmide design

Separates pure Logic from computational Host.

```
                    represents and
                      implements
      +--------------------+--------------------+
      |                    |                    |
      |                    |                    |
      v                    |                    |
Logic Magmide              +-------------> Host Magmide
      |                                         ^
      |                                         |
      |                                         |
      +-----------------------------------------+
                    logically defines
                      and verifies
```

<v-clicks>

- C -> Rust
- Coq/LLVM -> Magmide
- Currently bootstrapping prototype
- Coq for initial proofs and LLVM for compilation

</v-clicks>

<style>
.slidev-layout {
  @apply pl-[16rem] pr-[10rem] py-[2rem] text-xl;
}
.slidev-code, pre {
  @apply text-xs !important;
}
</style>

---

# What's possible?

<v-clicks>

- Proof carrying code.
- Provably secure operating systems, firmware, network drivers, browsers, voting software...
- Safe package ecosystems.
- More advanced borrow checking algorithms.
- Approachable logic coach in many more hands.

</v-clicks>

---

# Thank you!

<br>

<v-click>

## [github.com/magmide/magmide](https://github.com/magmide/magmide)

</v-click>

<v-click>

<br>

# Software doesn't have to be so broken!

</v-click>
