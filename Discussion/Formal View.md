<H1>Formal View</H1>

%% insert note text below %%

# Clocks

Assume there exists an enumerable collection $\mathtt{clock}$ of atomic entities called clocks.

Assume also that the Leibniz equality for clocks is decidable. It means the existence of an algorithm recognizing whether any two clocks $c_1$ and $c_2$ are equal or not.

[[Enumerability]] of $\mathtt{clock}$ guarantees the existence of a bijection between $\mathtt{clock}$ and the set of natural number $\mathbb{N}$.
We fix one of such a bijection and denote it by $\mathtt{toNat}:\mathtt{clock}\to\mathbb{N}$.
We use the notation $\mathtt{nthClock}$ for the function $\mathtt{toNat}^{-1}:\mathbb{N}\to\mathtt{clock}$.

Given these considerations, we model the set of all clocks as the following inductive type.

```
Inductive clock : Set := nthClock : nat -> clock.
````

Also, we define the coercion as follows

```
Coercion toNat := fun c : clock => let 'nthClock n := c in n.
```

# Clock Sets

Also, we consider finite sets of clocks, which are called clock sets.
For referring to the set of all clock sets, the denotation $\mathtt{ClockSet}$ is used.

The use of function $\mathtt{toNat}$ provides to model an element of $\mathtt{ClockSet}$ by a list of clocks with the property of increasing i. e. $\mathtt{toNat}\\,c'<\mathtt{toNat}\\,c''$ if the position of $c'$ in such a list is less than the position of $c''$ in this list.<br/>
That is, the model of the set $\mathtt{ClockSet}$ is the following type

```
Definition ClockSet := {cs : list clock | increasing cs}
```
where the predicate `increasing: list clock -> Prop` is defined as follows

```
Inductive increasing : list clock -> Prop :=
  | inc0 : increasing []
  | inc1 : forall c, increasing [c]
  | incS : forall c1 c2 cs, toNat c1 < toNat C2 -> increasing (C2 :: cs) -> increasing (c1 :: c2 :: cs).
```
For $\mathtt{ClockSet}$, we the coercion

```
Coercion toList := fun cs : ClockSet => proj1_sig cs. 
