---
theme: apple-basic
class: text-center
highlighter: prism
lineNumbers: false
drawings:
  persist: false
---

<h1>Software can literally<br>be perfect</h1>

<h2>How Formal Verification and Magmide<br>could make provably correct code<br>attainable for practicing software engineers.</h2>

<style>
.slidev-layout {
  @apply px-[4rem] py-[8rem];
}
.slidev-layout h1 {
  @apply text-5xl mb-[4rem];
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

# Software is broken

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
  @apply px-[10rem] py-[2rem] text-lg;
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

# It doesn't have to be this way!

Provably correct code is possible with formal verification.

[Quanta Magazine: Hacker-Proof Code Confirmed](https://www.quantamagazine.org/formal-verification-creates-hacker-proof-code-20160920/)

<img class="h-[30vh]" src="https://d2r55xnwy6nx47.cloudfront.net/uploads/2016/09/ProgramVerification_BoyaSun_2K.jpg" />

<style>
.slidev-layout {
  @apply px-[12rem] py-[4rem];
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

# Core concepts of formal verification

- Dependent Types
- Type Checking is Proof Checking
- Separation Logic

<!--
introduce core concepts
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

<style>
.slidev-layout {
  @apply text-3xl;
}
</style>

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

<!--
coq
this isn't a coq lesson, so you don't have to deeply understand this function, I just want you to realize it's possible
this function does what we want
here's how to read function type
it's long, but it works!
-->

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

<v-click>

The *type system* checks that everything is consistent.

</v-click>

<!--
a type system that has dependent types basically makes *type* checking the exact same thing as *proof* checking
to check whether some proof is actually consistent, we just run our type checking algorithm
the cool thing is that this is actually true for *any* type checking algorithm. all type systems, such as Rust's type system, are just "logical" systems, and when you write code and assert that code has a certain type, the type checking algorithm is basically checking if your "proof" is correct
simpler type systems are basically equivalent to simpler logical systems, so they can't make claims and proofs about very interesting logical ideas
this is lame, but can be more powerful
-->

---

```v
Inductive Even: nat -> Prop :=
  | Even_0: Even 0
  | Even_plus_2: forall n, Even n -> Even (S (S n)).
```

<v-click>

```v
Definition four_is_even: Even 4.
Proof.
  repeat constructor.
Qed.
```

</v-click>

<!--
here's a slightly more interesting example
again, the purpose of this talk isn't to teach you how to use Coq, it's just to let you know what's possible
here we're defining our own type, and the way we've defined the type means we can use it to make claims about numbers being Even
basically we've defined a set of rules, ones that we completely made up, about what it means for a number to be even, and this set of rules can be used to *construct* proofs that some particular number is even
then we can prove that particular numbers are even, again don't worry about exactly how this is working
I'm using Coq's interactive tactic system to metaprogrammatically construct an object that proves that 4 is even
-->

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

<!--
we can prove more interesting things though
double is a function that doubles a natural number, using recursion
and we can prove that if you double any natural number, the result is even
under the hood, even_double is just a function
it transforms values of a the type natural number into a proof that that doubling that specific natural number is even
-->

---

# If you want to learn more:

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


<!--
very powerful
-->

---

# Why isn't everyone doing this?

<v-clicks>

- Research Debt
- Pure Functional Dogma

</v-clicks>

<!--
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

> The insidious thing about research debt is that it’s normal. Everyone takes it for granted, and doesn’t realize that things could be different.

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

<!--
research debt is a big problem

read quotes
culture of academia
jargon terseness
toxic, feels intentionally exclusive

but research debt isn't the *main* problem
-->

---

# Pure Functional Dogma

<v-clicks>

- No mutation or side effects.
- But it's always a lie!
- Computers are just big chunks of mutable state.

</v-clicks>

<!--
the real problem has been pure functional dogma
really quick, what is the pure functional paradigm?
it's this
it's a lie!
real computation is imperative, it mutates state

the real problem is that these systems have never been truly practical!
practicing engineers trying to build real systems that they can actually ship to accomplish some goal just couldn't use these techniques
my theory about why that's remained true is because these techniques have unproductively focused almost exclusively on the pure functional paradigm
in order to make formal verification mainstream, we have to be able to prove things about realistic imperative programs
need system for mutable state
-->

---

# Separation Logic

Logical framework for reasoning about mutable state.

<!--
separation logic was invented for this purpose
I'm surprised how often people who've heard of proof languages haven't heard of separation logic
but first we have to understand the normal logical systems it's responding to
-->

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

<!--
conjunction is the academic name for the logical "and" operation.
conjunction
*pure* propositions, duplicable
freely duplicate P
-->

---

```
Even(4) ∧ (1 + 1 = 2)
equivalent to:
(Even(4) ∧ (1 + 1 = 2)) ∧ Even(4)
```

<!--
pure logical facts
-->

---

```
a --> 1
```

<v-click>

<br>

memory location `a` points to `1`

</v-click>

---

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

<!--
but for resources? can change or be destroyed?
Rust's ownership system was directly inspired by separation logic.
easy to create inconsistent situations
rules don't stop you early enough
verification researchers were using this kind of approach before separation logic, and it made proofs about program correctness extremely tedious and basically impossible to scale
you had to make assertions about the state of the *entire* program, rather than being able to make assertions about little pieces of the program and compose them together
-->

---

```
// Not Allowed! ❌
(a --> 1) * (a --> 1)
```

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

<!--
back to separation logic
*separating* conjunction
use star, pronounced "and separately"
must be disjoint
even when consistent
assertions are *disjoint*, or separate
can't duplicate
have to give away knowledge, or ownership
this disjointness requirement is surprisingly powerful, it makes it so it's possible to make assertions about just one little piece of the program, knowing that if another piece of the program gives you knowledge about some piece of state, no one else can mess with that state but you!
other more complex ideas flow from the disjointness concept, separating implication, frame rule

but what about multiple read only?
what about concurrency or atomics?
-->

---

# Rust

<v-clicks>

- Rust borrow checker: proof checker for a *subset* of a fractional separation logic.
- Need `unsafe` for it to actually be realistic and useful.
- Can't reason about correctness of `unsafe` code.

</v-clicks>

<!--
like I mentioned, the rust ownership and lifetime system, which is checked by the borrow checker, is directly inspired by separation logic
separation logic
-->

---

# Iris Separation Logic

<v-clicks>

- Built to verify arbitrarily complex Rust programs.
- Written in Coq.
- [Iris from the ground up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)
- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)
- Type system, ownership and lifetimes, `Send` and `Sync`
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

<!--
core ideas are learnable
mired in academic jargon, obtuse notation
only used in academic work
only "on the side proofs"
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

<v-clicks>

- Rust -> C
- Magmide -> Coq and LLVM

</v-clicks>

<v-click>

http://github.com/magmide/magmide

</v-click>

<v-click>

Thank you!

</v-click>

<style>
.slidev-layout {
  @apply pl-[16rem] pr-[10rem] py-[3rem] text-xl;
}
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
