---
theme: seriph
background: >-
  https://images.unsplash.com/photo-1620837953336-8274c0623a3c?ixlib=rb-1.2.1&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=3870&q=80
class: text-left
highlighter: prism
lineNumbers: false
drawings:
  persist: false
---

<h1 class="text-left text-2xl">Software can literally be perfect</h1>

<h2 class="text-left text-xl">Dependent Types</h2>
<h2 class="text-left text-xl">Separation Logic</h2>
<h2 class="text-left text-xl">Iris</h2>
<h2 class="text-left text-xl">Magmide</h2>
<h2 class="text-left text-xl">and the path to provably correct code</h2>

<style>
.slidev-layout {
  @apply px-[4rem] py-[2rem];
}
</style>

<!--
formal verification, what it is
what big ideas are
practical and mainstream

this talk is intended for people who already understand type systems, and understanding the Rust type system is really helpful
you don't have to be good at Rust, but understanding how its type system works will make this talk way easier to understand
-->

---

**Software is broken.**

- security breaches
- ransomware attacks
- operational failures
- safety critical failures

[The Cost of Poor Software Quality in the US: A 2020 Report](https://www.it-cisq.org/pdf/CPSQ-2020-report.pdf)

- $1.56 trillion in operational failures
- $1.31 trillion in technical debt

[The Hidden Costs of Cybercrime](https://www.mcafee.com/enterprise/en-us/assets/reports/rp-hidden-costs-of-cybercrime.pdf)

- $945 billion monetary loss from cybercrime
- $145 billion global spending on cybersecurity

Broken software hurts people, and slows down human progress.

<style>
.slidev-layout {
  @apply px-[10rem] py-[2rem];
}
</style>

<!--
obvious software is broken
it's a problem
all of us deal with it every day

Consortium for Information & Software Quality | The Cost of Poor Software Quality in the US: A 2020 Report
$1.56 trillion costs for operational failures, just for the US in 2020
$1.31 trillion *separately* for technical debt in critical software

McAfee | Hidden Costs of Cybercrime
https://www.mcafee.com/enterprise/en-us/assets/reports/rp-hidden-costs-of-cybercrime.pdf
up from $522.5 billion in 2018
-->

---


It doesn't have to be this way!

Provably correct code is possible with formal verification.

[Hacker-Proof Code Confirmed](https://www.quantamagazine.org/formal-verification-creates-hacker-proof-code-20160920/)

<img class="h-[30vh]" src="https://d2r55xnwy6nx47.cloudfront.net/uploads/2016/09/ProgramVerification_BoyaSun_2K.jpg" />

<v-click>

I challenge you to use any of the tools they built!

</v-click>

<style>
.slidev-layout {
  @apply px-[6rem] py-[4rem];
}
</style>

<!--
DARPA funded team
unhackable quadcopter control software
even after world class hacking team given access
formal verification, proofs
however the team that did that were all phds
we don't all have time for obtuse academic papers
-->

---

# Magmide

- Bring formal verification to practicing engineers.
- Proof language as a verified bare metal program.
- Foundation for verified programs for any architecture or environment.

<!--
formal verification needs to be brought out of the ivory tower
but in order to believe the goals of Magmide are possible, and to realize why the design of Magmide is exciting, it's useful to understand the core concepts behind formal verification
-->

---

The core concepts of formal verification:

- Dependent Types
- Type Checking is Proof Checking
- Separation Logic

<!--
introduce core concepts
Iris
Magmide
first dependent types
-->

---

```rust
fn is_one(n: u64) -> bool {
  n == 1
}
```

<v-click>

`(u64) -> bool`

</v-click>

<!--
to understand dependent types, first let's look at a problem
is_one
type of this function
know nothing about meaning of bool
-->

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

<!--
same type, different behaviors
can we be certain?
testing can't do it, at least not for infinite inputs
can the type of the function?
this is where dependent types come in
a dependent type system is one that allows *types* to reference, or *depend* on *values*
-->

---

# Dependent Types

```v
Require Import Coq.Program.Tactics Coq.micromega.Lia.

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

<style>
.slidev-code {
  @apply text-base !important;
}
</style>

<!--
coq
I'm intentionally not worried if you understand this function, I just want you to realize it's possible
this function does what we want
here's how to read function type
it's long, but it works!
this is lame, but can be more powerful
more ideas, dependent types are the core one
-->

---

# Programs == Proofs

<v-click>

Is `0` a proof?

</v-click>

<v-click>

More specifically, is `0u64` a proof?

</v-click>

<v-click>

Yes, a proof of `u64`!

</v-click>

So is 1, 42, 250, etc

<v-click>

Curry-Howard Correspondence

</v-click>

<!--
programs and proofs are the same thing

is 0 a proof? 0 isn't a very interesting program, but it's a program
yes, 0 is a proof! more specifically in Rust, the literal 0u64 is a *proof* of of u64
all I'm doing is using different words for things we already understand
if we change our perspective so that a *type* is the same as a *proposition*, a logical assertion that can possibly be proven
then any piece of *data* that typechecks as some type is a *proof* of the proposition represented by that type

this is a bit mind-bending, but it's true for any programming language!
not all programming languages can prove very interesting things, but they can all prove things
-->

---

# Programs == Proofs

<v-clicks>

- `0u64` proves `u64`
- `true` or `false` prove `bool`
- `0u64` or `true` or `false` proves `u64 | bool`
- `(0u64, true)` proves `(u64, bool)`

</v-clicks>

<!--
different patterns of types can prove different kinds of propositions
-->

---

# Programs == Proofs

```v
Inductive Bit :=
  | bit0
  | bit1.

Inductive Byte :=
  | byte (b7 b6 b5 b4 b3 b2 b1 b0: Bit).

Definition binary_zero: Byte :=
  (byte bit0 bit0 bit0 bit0 bit0 bit0 bit0 bit0).
```

<v-click>

- `binary_zero` is a *value* of `Byte`
- `binary_zero` is a *proof* of `Byte`

</v-click>

<!--
here's how we'd actually declare the type of a byte in Coq
first we have to define the concept of a bit
and then a byte is just a tuple of bits!
there's only one way to "prove" byte, by "proving" eight bits
but there are two ways to "prove" a bit, either with the zero version or the one version
we can think of pieces of data as "evidence" of some proposition
-->

---

# Programs == Proofs

```v
Inductive Even: nat -> Prop :=
  | Even_0: Even 0
  | Even_plus_2: forall n, Even n -> Even (S (S n)).
```

<v-click>

```v
Definition even_4_manual: Even 4 :=
  (Even_plus_2 2 (Even_plus_2 0 Even_0)).
```

</v-click>

<v-click>

```v
Theorem even_4: Even 4.
Proof.
  repeat constructor.
Qed.
```

</v-click>

<!--
because of dependent types, it's possible to create a language where *type* checking is the same as *proof* checking


dependent types are what makes this programs equals proofs concept actually powerful though
here's a more interesting Even type
Even is kind of like bit, in that it has two constructors, or two ways to construct "data" or a "proof" of Even
the first one, Even_0, can only prove that 0 is even
but the second one Even_plus_2, is a *function* that if you pass it a proof that some number n is Even, it will give you back a proof that the number plus two is even
(S (S n)) is the weird coq way of writing plus 2, it's basically incrementing twice, don't worry about it
I'm skipping lots of details, you can go learn more

using our even constructors, we can construct a piece of evidence whose *type* is that 4 is even
at the bottom is a proof that 0 is even, and then we call the plus two constructor twice on top of that

most of the time manually writing out the actual proof object is tedious, so we can use these interactive tactics
they're basically just metaprograms that construct values of different types
-->

---

# Programs == Proofs

<v-click>

```rust
fn is_one(n: u64) -> bool {
  n == 1
}
```

- `is_one` is a *value* of `u64 -> bool`

</v-click>

<v-click>

| P | Q | P -> Q |
|---|---|--------|
| T | T | T      |
| T | F | F      |
| F | T | T      |
| F | F | T      |

- `is_one` is a *proof* of `u64 -> bool`

</v-click>

<!-- <v-click>

```rust
fn always_true(_: u64) -> bool {
  n == 1
}
```

</v-click> -->


<!--
where this really gets powerful, is *functions* that can transform evidence into different pieces of evidence
remember our simple rust function is_one
the type of this function is u64 -> bool
in programming languages we read that type as the function type, basically an indication that we can take a value of some type and transform it into a value of another type
using the types as propositions concept again though, we can just use different words and treat the arrow as *logical implication*

again though, u64 -> bool isn't a very interesting type, lots of functions that do different things have that same type
-->

---

```v
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S sub_n => S (S (double sub_n))
  end.
```

<v-click>

```v
Theorem even_double: forall n, Even (double n).
Proof.
  induction n; constructor; assumption.
Qed.
```

</v-click>

<!--
with dependent types, especially more interesting ones like Even
a *function* can be a *logical theorem* that proves something
if you double any number result is even
even_double is just a function
it transforms values of a the type natural number into a proof that that doubling that specific natural number is even
-->

---

```v
Definition even_double_manual :=
  fun n: nat => nat_ind
  (fun n0: nat => Even (double n0)) Even_0
  (fun (n0: nat) (IHn: Even (double n0)) =>
   Even_plus_2
     ((fix double (n1: nat): nat :=
        match n1 with
        | 0 => 0
        | S sub_n => S (S (double sub_n))
        end) n0) IHn) n.
```

<!--
here's the raw function
-->

---

If you want to learn more:

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/)

<!--
very deep topic
-->

---

Dependently typed proof languages are extremely powerful:

- [Feit–Thompson theorem](https://en.wikipedia.org/wiki/Feit%E2%80%93Thompson_theorem)
- [DeepSpec](https://deepspec.org/main)
- [HACMS: High Assurance Cyber Military Systems](https://loonwerks.com/projects/hacms.html)
- [Project Everest](https://project-everest.github.io/)

<v-click>

Why isn't everyone doing this?

</v-click>

<!--
very powerful
why aren't these tools widely used?
two big reasons
-->

---

# [Research Debt](https://distill.pub/2017/research-debt/) - Chris Olah, Shan Carter

> There’s a tradeoff between the energy put into explaining an idea, and the energy needed to understand it. On one extreme, the explainer can painstakingly craft a beautiful explanation, leading their audience to understanding without even realizing it could have been difficult. On the other extreme, the explainer can do the absolute minimum and abandon their audience to struggle. This energy is called interpretive labor.

<v-click at="1">

> People expect the climb to be hard. It reflects the tremendous progress and cumulative effort that’s gone into mathematics. The climb is seen as an intellectual pilgrimage, the labor a rite of passage. But the climb could be massively easier. It’s entirely possible to build paths and staircases into these mountains. The climb isn’t something to be proud of.

> The climb isn’t progress: the climb is a mountain of debt.


</v-click>

<v-click at="2">

> The insidious thing about research debt is that it’s normal. Everyone takes it for granted, and doesn’t realize that things could be different. For example, it’s normal to give very mediocre explanations of research, and people perceive that to be the ceiling of explanation quality. On the rare occasions that truly excellent explanations come along, people see them as one-off miracles rather than a sign that we could systematically be doing better.

</v-click>

<v-click at="3">

Academia has bad incentives to properly explain and expose their work.

</v-click>

<style>
.slidev-layout {
  @apply px-[6rem] pt-[4rem] pb-[5rem];
}
</style>

<!--
read quotes
culture of academia
jargon terseness
toxic, feels intentionally exclusive
-->

---

# Pure Functional Dogma

Outlawing mutation and side effects gives a model of computation the same cleanliness as pure logic.

<v-click>

But it's always a lie!

</v-click>

<v-click>

Von Neumann computation is *defined* as effectful mutation of state.

</v-click>

<!--
metaprogramming not used when in lisp and scheme, very widely used in Rust
discriminated union types not used when in ml and haskell, very widely used in Rust
proof languages are pure functional
that makes sense for mathematical proofs, but clearly it isn't sufficient
need system for mutable state
-->

---

# Separation Logic

Logical framework for reasoning about mutable state.

<!--
separation logic was invented for this purpose
but first we have to understand the normal logical systems it's responding to
-->

---

# ... Normal Logic

```
P ∧ Q
// we could write it with an "and" symbol if we want
P & Q
```

<v-click>

(logical "or" operation is called *disjunction* by academics, P ∨ Q)

</v-click>

<v-click>

```
P ∧ Q
equivalent to:
(P ∧ Q) ∧ P
```

</v-click>

<!--
conjunction is the academic name for the logical "and" operation.
conjunction
*pure* propositions, duplicable
freely duplicate P
-->

---

```
Even(4) ∧ (1 + 1 == 2)
equivalent to:
(Even(4) ∧ (1 + 1 == 2)) ∧ Even(4)
```

<!--
pure logical facts
-->

---

```
mem[a] == 1
```

<v-click>

```
???
(mem[a] == 1) ∧ (mem[a] == 2)
```

</v-click>

<!--
but for resources? can change or be destroyed?
Rust's ownership system was directly inspired by separation logic.
easy to create inconsistent situations
rules don't stop you early enough
-->

---

```
// Not Allowed! ❌
(mem[a] == 1) * (mem[a] == 1)
```

<div class="h-20"></div>

<v-click>

```
// Okay! ✅
(mem[a] == 1) * (mem[b] == 2)
```

</v-click>

<!--
back to separation logic
*separating* conjunction
use star, pronounced "and separately"
must be disjoint
even when consistent
assertions are *disjoint*, or separate
can't duplicate
have to give away knowledge, or ownership
other ideas, separating implication, frame rule

but what about multiple read only?
what about concurrency or atomics?
-->

---

# Rust

Rust borrow checker a proof checker for a *subset* of separation logic.

(All type checkers are proof checkers, just for very simple logical systems.)

Need `unsafe` for it to

<!--
like I mentioned, the rust ownership and lifetime system, which is checked by the borrow checker, is directly inspired by separation logic
separation logic
-->


---

# Iris

Built to verify arbitrarily complex Rust programs.

[Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)

[RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)

<v-clicks>

- Type system, including ownership and lifetimes, `Send` and `Sync`
- `Arc`, `Rc`, `Cell`, `RefCell`, `Mutex`, `RwLock`, `mem::swap`, `thread::spawn`, `rayon::join`, `take_mut`

</v-clicks>

<!--
basic ideas are just the beginning
more complex versions for about 20 years
Iris
used to verify soundness of Rust type system
*and even to verify the correctness of code that uses `unsafe`*!
-->

---

Why isn't everyone using Iris?

- Still lots of research debt.
- No directly usable tool.

<!--
core ideas are learnable
mired in academic jargon, obtuse notation
only used in academic work
only "on the side proofs"
(TODO side by side example)
-->

---

# Magmide

Design constraints:

<v-clicks>

- Fully verifiable (represent any assertion)
- Abstractly bare metal (represent any program)
- Incrementally adoptable (allow realistic iteration)
- Metaprogrammatically reusable (verification pyramid)
- Practical and usable (prioritize tooling)
- Taught effectively (respect user's time)

</v-clicks>

<!--
Can formal verification be practical?
core ideas
Rust succeeded by making big promises, give full logical power
a logical system can formalize any environment, we might as well
trackable effects use an idea from Iris/Iron, trackable invariants
languages can create reusable safety guarantees for sub-languages, reexpose proof language, combine upward
rust and cargo are great
prioritize distillation research, no obtuse notations, no jargon, no non-ascii characters, examples before formal definitions
-->

---

# Magmide

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

<v-click>

- C -> Rust
- Coq/LLVM -> Magmide

</v-click>

<v-click>

http://github.com/magmide/magmide

</v-click>

<v-click>

Thank you!

</v-click>

<style>
.slidev-code, pre {
  @apply text-xs !important;
}
</style>

<!--
the current state of affairs is unacceptable
I've shared core ideas in this short talk, not impossible to learn
get formal verification out of the ivory tower
software has been broken for too long
should be practical and reusable for software practitioners

Magmide will combine pure proof language with practical computational language, with Iris
could verify software for any environment
deeply embedded systems
webassembly runtime

repo
very early, only exploratory proofs, design writing, Coq plugin for bootstrapping
feedback and support welcome!
hope you're inspired!
-->
