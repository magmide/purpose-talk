---
theme: seriph
# random image from a curated Unsplash collection by Anthony
# like them? see https://unsplash.com/collections/94734566/slidev
# background: https://images.unsplash.com/photo-1620837953336-8274c0623a3c?ixlib=rb-1.2.1&ixid=MnwxMjA3fDB8MHxwaG90by1wYWdlfHx8fGVufDB8fHx8&auto=format&fit=crop&w=3870&q=80
# apply any windi css classes to the current slide
class: 'text-left'
# https://sli.dev/custom/highlighters.html
highlighter: prism
# show line numbers in code blocks
lineNumbers: false

# persist drawings in exports and build
drawings:
  persist: false
---

<h1 class="text-2xl">Software can literally be perfect</h1>

<h2 class="text-xl">Dependent Types</h2>
<h2 class="text-xl">Separation Logic</h2>
<h2 class="text-xl">Iris</h2>
<h2 class="text-xl">Magmide</h2>
<h2 class="text-xl">and the path to provably correct code</h2>

<style>
.slidev-layout {
  @apply px-[4rem] py-[2rem];
}
</style>

---

**Software is broken.**

- security breaches
- ransomware attacks
- operational failures
- safety critical failures

Broken software hurts people, and slows down human progress.

<!--
honestly I'm not going to spend much time trying to convince you this is true.
you already know its true just because you live in our society
you deal with broken software all the time

https://www.it-cisq.org/pdf/CPSQ-2020-report.pdf
Consortium for Information & Software Quality | The Cost of Poor Software Quality in the US: A 2020 Report
$1.56 trillion costs for operational failures, just for the US in 2020
$1.31 trillion *separately* for technical debt in critical software

https://findstack.com/hacking-statistics/
Cybercrime costs the world economy more than $1 trillion per year (McAfee)
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
this article talks about a DARPA funded team that was able to create control software for a quadcopter, that couldn't be hacked into, even by the best hackers in the world, people who can usually commandeer jeeps and make atms pay them arbitrary amounts of money.
the team did this by *proving*, with the same level of certainty as you would prove that 1 + 1 = 2, that the control software was impossible to remotely hijack.
however the team that did that were all phds
not all of us have the time to wade through academic jargon and use the punishingly obtuse tools academics build
at least for non-professors
-->

---

The core concepts of formal verification aren't very complicated.

- Dependent Types
- Proof Objects
- Separation Logic

<!--
this talk intends to discuss the basic concepts that make provably correct code possible
and talk about Magmide, a language intended to make formal verification practical for practicing software engineers
The first idea is dependent types
before understanding what they are, let's understand why we might want them
-->

---

# Dependent Types

```rust
fn is_one(n: u64) -> bool {
  n == 1
}
```

<v-click>

`(u64) -> bool`

</v-click>

<!--
this rust function returns a boolean indicating whether some unsigned number is 1
the *type* of this function is `(u64) -> bool`, which tells us nothing about the meaning of this function. we don't know what the returned bool *means* just that we get a bool
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
But notice that the *type* `(u64) -> bool` can apply to *many* different functions, all of which do different things:
what if we wanted a way to be *certain* that our function did what it said? we could test it, but then we would only be able to be certain about all the inputs we could actually come up with and feed into the function. what if we wanted the *type* of the function to guarantee its behavior?
this is where dependent types come in
a dependent type system is one that allows *types* to reference, or *depend* on *values*
-->

---


```v
Require Import Coq.Program.Tactics Coq.micromega.Lia.

Program Definition is_one n: {b | b = true <-> n = 1} :=
  match n with
  | 1 => true
  | _ => false
  end
.
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
Here's a function in the dependently typed proof language Coq. It's quite a mouthful, but it does the thing we want.
The type of this function is: `forall (n: nat), {b: bool | b = true <-> n = 1}`, which is read as "forall n which is a nat (natural number), return a b which is a bool such that b is true if and only if n = 1"
It would be nice if that type wasn't so long, but it works! Using Coq and the the `lia` tactic (which can automatically solve lots of simple math problems, it stands for "linear arithmetic"), we can write a function that is *provably correct*.
Of course guaranteeing a function always correctly says if a number is 1 is pretty lame, but you can do much more powerful things using a proof language like Coq.
there are quite a few more important concepts that make coq and languages like it powerful, but dependent types are the main idea at the heart of them all.
-->

---

# Proof Objects

Is `0` a proof?

<v-click>

Yes! A proof of `u64`!

</v-click>

<v-clicks>

- `0` proves `u64`
- `true` proves `bool`
- `is_zero` proves `u64 -> bool`
- `(0, true)` proves `(u64, bool)`
- `0` or `false` proves `u64 | bool`

</v-clicks>

<!--
these kinds of dependently typed proof languages are extremely powerful. it's a programming language that is literally nothing more than *type theory*, a system of logic powerful enough to define all of mathematics

in a system like this you can state basically arbitrary propositions of logic as *programs*. essentially, a type can be the same as a *proposition*, and a piece of data that successfully checks as that type is a *proof* of that proposition.
-->

---

```v
Inductive Even: nat -> Prop :=
  | Even_0: Even 0
  | Even_plus_2: forall n, Even n -> Even (S (S n))
.
```

<v-click>

```v
Theorem even_4: Even 4.
Proof.
  repeat constructor.
Qed.
```

</v-click>

<v-click>

```v
Definition even_4_manual: Even 4 :=
  (Even_plus_2 2 (Even_plus_2 0 Even_0)).
```

</v-click>

<!--
I'm not going to go over all the details, I'm just trying to let you know all of this is possible. go learn more if you want
for a small taste, here's a *type* that can be used to build a proof object, or "evidence", that some number is even
we can prove things about even numbers, from simply asserting that some particular number is even
-->

---

```v
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S sub_n => S (S (double sub_n))
  end.

Theorem even_double: forall n, Even (double n).
Proof.
  induction n; constructor; assumption.
Qed.
```

<!--
to the fact that if you double any number the result will be even
-->

---

If you want to learn more:

- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/)

<!--
this is an extremely deep topic, so if you want to learn more go check out these resources
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
it should be obvious this is extremely powerful. we can see teams doing lots of amazing things with proof assistants
so if this is so powerful, why isn't is commonplace? why isn't everyone doing this? there are two big reasons
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
all this cool work is hopeless mired in *research debt*. basically academia has really bad incentives about actually making research understandable and discoverable by everyone else. they have a really weird specific culture that values jargon and being as terse as possible instead of making things as easy to learn as possible. I honestly think the culture of academia is actually kind of toxic, it seems like they're almost willfully unconcerned with letting anyone who isn't already in the club understand what they're doing.
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
they're also way too dogmatic about the *pure functional paradigm*. there are so many really useful ideas that started in academia and then sat mostly ignored for a long time in pure functional languages before finally being put into imperative languages and finding mainstream adoption.
the concept of metaprogramming is extremely powerful, and it was a curiosity in lisp and scheme and such things before Rust brought it into standard practice.
discriminated union types and the match block are extremely poweful, but that idea was a curiosity of ml and haskell until, again, Rust made everyone see how powerful it was.
all these proof languages are pure functional languages. I'll actually talk later about why the pure functional paradigm is perfectly suited to *proof* languages.
but we need a rigorous logical system for reasoning about real computational state, which is mutable and finite.
-->

---

# Separation Logic

Logical framework for reasoning about mutable state.

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
separation logic is a logical framework for making rigorous assertions about mutable state. it's a perfect fit for reasoning about *real* computation, since a computer is just a big chunk of mutable state. in fact, Rust's ownership system was directly inspired by separation logic.
the core idea of separation logic is the *separating conjunction*, but in order to understand it we'll have to talk about the *normal* conjunction.
conjunction is the academic name for the logical "and" operation.
if we have two logical assertions P and Q, then if we want to assert that *both* of them are true we will try to prove their *conjunction*
conjunction works great for *pure* propositions, ones that are inherently *duplicable*, since we can do things like this:
we can freely copy the P, and the two logical statements are perfectly equivalent
-->

---

```
Even(4) ∧ (1 + 1 == 2)
equivalent to:
(Even(4) ∧ (1 + 1 == 2)) ∧ Even(4)
```

<!--
if our assertions are pure facts, maybe P = Even(4) and Q = 1 + 1 == 2, then this works great
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
but what if our assertion is talking about some *resource*, an assertion about something that could *change* or be destroyed, such as an assertion about a memory location, mem[a] == 1
this can still work, but it could be really easy to accidentally assert something false, such as (mem[a] == 1) ∧ (mem[a] == 2)
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
so separation logic was invented. instead of a normal conjunction operator that allows you to duplicate assertion, it has the *separating* conjunction (written with a star, `*`, pronounced "and separately"), which basically requires that different assertions aren't allowed to talk about the same pieces of state.
for example, it's not allowed for the separating conjunction to be used on assertions that talk about the same piece of memory, even if the assertions are consistent with each other
the assertions have to be *disjoint*, or separate (which is why it's called separation logic)
this means that you can never duplicate an assertion about the same spot in memory, in order to pass a function an assertion you either have to make a fresh copy of the data in a new place or *give the assertion away*. this is why an assertion in separation logic nicely encodes *ownership* of finite resources, resources that can be created, mutated, and destroyed. there are a few more concepts in separation logic, such as the separating implication and the frame rule, but the separating conjunction is the main idea.
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
but of course, separation logic is just a handful of ideas, and the simple description I've given you is way too strict to really be useful. what if I want to give a read-only reference to someone without losing my own knowledge of it? what if I'm using atomic updates and so I can have multiple threads make writes at the same time?
the basic ideas of separation logic are just the beginning, and people have been making more specific, and complex, versions of it for about twenty years.
recently, a team of academics created the Iris separation logic, which is powerful enough that they were able to verify the correctness of the Rust type system, *and even to verify the correctness of code that uses `unsafe`*! it's a framework so powerful that it can verify even insanely complicated things
-->

---

Why isn't everyone using Iris?

- Still lots of research debt.
- No directly usable tool.

<!--
but again, *research debt* rears its head. Iris is extremely powerful, and although the core concepts that would allow a practicing engineer to use it aren't that complicated, actually understanding the tool is incredibly challenging. it's mired in academic jargon and difficult to parse notation.
the most troubling thing is that Iris is only being used to write papers, only being used in theoretical models and academic work, and hasn't been built into a tool that practicing engineers would ever actually use to create shippable software.
all the proofs that these academic teams are doing on code aren't being done on *directly* on the real source code, but a Coq-notation translated version of it (TODO side by side example). these proofs are being done "on the side".
-->

---

Can formal verification be practical?

<v-clicks>

- Fully verifiable (represent any assertion)
- Abstractly bare metal (represent any program)
- Incrementally adoptable (allow realistic iteration)
- Metaprogrammatically reusable (verification pyramid)
- Practical and usable (prioritize tooling)
- Taught effectively (respect user's time)

</v-clicks>

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
I think all of this is unacceptable. I've skipped a lot of details, but even in this short talk I've explained the big ideas that can make provably correct code possible. I don't think we should tolerate these ideas being trapped in the ivory tower anymore, and I'm not willing to wait around for an academic to decide they want to build a practical and usable tool. software has been broken for too long, and it's causing immense harm every day. it's time to build something that can clear away all this research debt and make formal verification practical for everyone.
this is why I've been working on the Magmide project. the idea of Magmide is to create a tool that brings together a dependently typed pure functional proof language (Logic Magmide) and a practical bare metal computational language (Host Magmide) that places the full power of Iris at its core. the goal is for Magmide to be to both Coq and LLVM what Rust has been to C.
the combination of both a full dependently typed proof language and a bare metal host language would allow us to build verified software for *any* computational environment, from deeply embedded systems all the way up to hosted environments like that provided by the webassembly runtime
if you want to understand more about the Magmide design and the goals of the project, head over to the repo.
right now Magmide is extremely early, and I only have some exploratory proofs, a lot of design writing, and a Coq plugin I intend to use while the project is being bootstrapped. your feedback and help are welcome!
thank you for your time! I hope I've inspired you about the possibility of provably correct code, and that you'll come help me build Magmide!
-->
