import Mathlib
set_option quotPrecheck false
#print Group
--Ch 2. HILBERT'S AXIOMS
--INTRO:
--Hartshorne presents Hilbert's axioms in higher order logic.
--`Point` is a primitive ``sort (or type)``.
--`Line : (Point→Prop)→Prop` is a primitive relation.
-- `Line` is a ``2nd-order relation of 1-arity``.
--`L∈Line` abbreviates the propositions `Line L`.
--`L∈Line` reads `L is a line`; lines are thought of as sets of points.
--Lean has built in support for higher order logic via `Set`.
--`Set Point` is syntactic sugar for `Point→Prop`.
--`L: Set Point` means `L : Point→Prop` is a ``1st-order property``.
--Any set can be thought of as the extension of a property.
#print Set
--Sets have basic constructive principles supporting them in Lean.
open Set
--One is the usual axiom of extensionality.
example {T:Type} (S₁ S₂:Set T) : (∀x:T, x∈S₁ ↔ x∈S₂) → S₁=S₂ := ext
--`∀L∈Line, P L` abbreviates `∀L:Set Point, Line L → P L`.
--By definition, the comprehension axiom comes for free.
--I.e. for any property `P:Point→Prop`, there is a set `{p:Point ∣ P p}`.

--Sec 6. AXIOMS OF INCIDENCE
--A set of points `Point` and collection of subsets of points `Line`,
-- is an `Incidence_Geometery` iff the following axioms are satsified.
class Incidence_Geometery (Point : Type) (Line : Set (Set Point)) where
  I1 : ∀p₁ p₂:Point, p₁≠p₂ → ∃!L, Line L ∧ p₁∈L ∧ p₂∈L
  I2 : ∀L, Line L → ∃p₁ p₂:Point, p₁≠p₂ ∧ p₁∈L ∧ p₂∈L
  I3 : let Colinear (p₁ p₂ p₃:Point) : Prop := ∃L, Line L ∧ p₁∈L ∧ p₂∈L ∧ p₃∈L
    ∃p₁ p₂ p₃:Point, p₁≠p₂ ∧ p₁≠p₃ ∧ p₂≠p₃ ∧
    ¬ Colinear p₁ p₂ p₃
--This is one approach if we wish to prove model-theoertic results,
--using Lean as the meta-theory. However we only wish to prove results
--true in all incidence geometeries. Harthsone does ask model-theoretic
--questions. However, we ignore them, drop this approach, and add axioms.

axiom Point : Type
axiom Line : Set (Set Point)
--(I1) Every pair of distint points is contained in a unique Line.
axiom I1 : ∀p₁ p₂:Point, p₁≠p₂ → ∃!L, Line L ∧ p₁∈L ∧ p₂∈L
--(I2) Every line contains two distinct points.
axiom I2 : ∀L, Line L → ∃p₁ p₂:Point, p₁≠p₂ ∧ p₁∈L ∧ p₂∈L
--(def) Three points are `Colinear` iff they all lie on the same line.
--`Colinear` is a ``1st-order property of 3-artiy``.
def Colinear (p₁ p₂ p₃:Point) : Prop := ∃L, Line L ∧ p₁∈L ∧ p₂∈L ∧ p₃∈L
--(I3) There exist three (distinct) noncolinear points.
axiom I3 : ∃p₁ p₂ p₃:Point, p₁≠p₂ ∧ p₁≠p₃ ∧ p₂≠p₃ ∧
  ¬ Colinear p₁ p₂ p₃

--(6.1) Two distinct lines intersect at most on one point.
lemma Prop6_1 : ∀ᵉ(L₁∈Line)(L₂∈Line), L₁≠L₂ →
  ¬∃p₁ p₂:Point, p₁∈L₁ ∧ p₂∈L₁ ∧ p₁∈L₂ ∧ p₂∈L₂ ∧ p₁≠p₂ := by
  rintro L₁ hL₁ L₂ hL₂ hL ⟨p₁, p₂, h11, h12, h21, h22, hp⟩
  obtain ⟨L, ⟨_, _⟩, h⟩ := I1 p₁ p₂ hp; dsimp at h
  apply hL
  have := h L₁ ⟨hL₁, h11, h12⟩
  have := h L₂ ⟨by assumption, by assumption, by assumption⟩
  rw[this]; assumption

--(def) Parralell lines have either no points or all points in common.
--`Parallel` is a ``2nd-order property of 2-arity`.
def Parallel (L₁ L₂: Set Point): Prop
  := Line L₁ ∧ Line L₂ ∧ (L₁=L₂ ∨ ¬∃p:Point, p∈L₁ ∧ p∈L₂)
--(P) For each point `p` and line `L` there is at most one line
-- containing `p` parralell to `L`.
--Parallel axiom `P` that may or may not be used, and is thus defined.
--`P` is a ``0th-order property``, i.e. a proposition.
def P : Prop :=  ∀ᵉ(p:Point) (L∈Line), ¬∃L₁ L₂,
  p∈L₁ ∧ p∈L₂ ∧ Parallel L L₁ ∧ Parallel L L₂ ∧ L₁≠L₂


--Sec 6. Sud's Exercises (useful for future sections!)

--Here are alternative axiomatizations of `I2` and `I3`.
--The purpose is to make future proofs constructive.

--For every line, there exists three distinct points:
--two which lie on the line, and one which does not.
lemma SudI2 (l: Set Point) (_ :Line l) : ∃p₁ p₂ p₃:Point,
   p₃∉l ∧ p₂∈l ∧ p₁∈l ∧ p₁≠p₂ ∧ p₁≠p₃ ∧ p₂≠p₃ := by
  --Take any line `l`.
  --There are two disctinct points `A, B` on the line.
  obtain ⟨A, B, _, _, _⟩ := I2 l (by assumption)
  use A, B
  --To prove there exists a third, we proceed by contra.
  by_contra h
  push_neg at h
  --Note: pushing `¬` this way is intuisionstically valid.

  --`h` implies every point is contained in `l`.
  --This bit uses the law of excluded middle.
  have h : ∀P:Point, P∈l := by
    intro P
    by_contra hP
    specialize h P hP
      (by assumption)
      (by assumption)
      (by assumption)
      (by intro hA; rw [← hA] at hP; contradiction)
    rw [← h] at hP
    contradiction

  --Now we contradict `I3`.
  obtain ⟨p₁, p₂, p₃, _, _, _, hp⟩ := I3
  unfold Colinear at hp
  push_neg at hp
  --Note: this pushing of `¬` is also constructive.
  apply hp l
  · assumption
  repeat (· apply h)

--There exists a line.
--Note: this can be proven constructively.
lemma SudI3 : ∃l:Set Point, Line l := by
--Let `p₁, p₂, p₃` be non colinnear points.
  obtain ⟨p₁, p₂, p₃, _, _, _, hp⟩ := I3
  unfold Colinear at hp
--Since `p₁≠p₂`, there is a line containing them.
  obtain ⟨l, ⟨⟨_, _⟩, _⟩⟩ := I1 p₁ p₂ (by assumption)
  use l


--Sec 7. Axioms of Betweenness
--`Between : Point→Point→Point→Prop` is a primitive relation.
--`Between` is a ``1st-order relation of 3-arity``.
--`Between A B C` means `B` is between `A` and `C`.
axiom Between : Point → Point → Point → Prop
--(B1) If `A⋆B⋆C` then `A,B,C` are distinct points which
-- lie on the same line and `C⋆B⋆A`.
axiom B1 : ∀A B C:Point, Between A B C → A≠B ∧ A≠C ∧ B≠C ∧
  Between C B A ∧ ∃l:Set Point, l∈Line ∧ A∈l ∧ B∈l ∧ C∈l
--(B2) For distinct points `A,B`, there exists point `C`
-- such that `A⋆B⋆C`.
axiom B2 : ∀A B:Point, A≠B → ∃C:Point, Between A B C
--(B3) Given three distinct points on a line, one and only one of them
-- is between the other two.
axiom B3 : ∀A B C:Point, ∀l∈Line, A≠B ∧ A≠C ∧ B≠C ∧ A∈l ∧ B∈l ∧ C∈l →
   (Between A B C  ∧ ¬Between C A B ∧ ¬Between B C A) ∨
   (¬Between A B C  ∧ Between C A B ∧ ¬Between B C A) ∨
   (¬Between A B C  ∧ ¬Between C A B ∧ Between B C A)
--(B4) Let `A,B,C` be noncolinear points, none of which are contained in
-- a line `l`. If `l` contains a point `D` lying between `A,C`, then it
-- must contain a point lying either between `A,C` or `B,C` but not both.
axiom B4 (A B C:Point) (l: Set Point) (_ :Line l) (_ :¬Colinear A B C)
(_:A∉l) (_:B∉l) (_:C∉l): (∃D:Point, D∈l ∧ Between A D C) →
((∃D₁:Point, D₁∈l ∧ Between A D₁ B) ∧ (¬∃D₂:Point, D₂∈l ∧ Between B D₂ C)) ∨
((¬∃D₁:Point, D₁∈l ∧ Between A D₁ C) ∧ (∃D₂:Point, D₂∈l ∧ Between B D₂ C))

--(def) If `A,B` are distinct points then `Seg A B` is the set consisting
-- of points `A,B` and all those inbetween `A,B`.
--We define `Seg` on all points for simplicity; any result using seg will
-- usually have distinctness inferable from context.
--`Seg` is a ``2nd-order function of 2-arity`.
def Seg (A B :Point) : Set Point :=
  { P | (fun X ↦ X=A ∨ X=B ∨ Between B X A) P }
--(def) If `A,B,C` are noncolinear points, then `Tri A B C` is the union
-- of segements `A↑B, A↑C, B↑C`. Think of `Tri A B C` as the boundary
-- of a 2-simplex. Again we define `Tri` on all points and expect
-- any context involving triangles to prove noncolinearity.
--`ΔABC` denotes `Tri A B C`.
--`Tri` is a ``2nd-order function of 3-arity``.
def Tri (A B C:Point) : Set Point :=
  Seg A B ∪ Seg A C ∪ Seg B C
notation:85 "Δ" A:85 B:85 C:85 => Tri A B C
--Note: Segements `Seg A B` and `Seg B A` are equal.
lemma Note7_1 (A B:Point) : Seg A B = Seg B A := by
  unfold Seg; apply ext; intro x
  constructor
  repeat intro h; simp only [mem_setOf]; obtain (_ |_ | h3) := h;
  · right; left; assumption
  · left; assumption
  · right; right
    obtain ⟨ _, _, _ ,mark, _⟩  := B1 B x A h3
    exact mark
  · simp; rintro (_ | _ | h3);
    · right; left; assumption
    · left; assumption
    · right; right
      obtain ⟨ _, _, _ ,mark, _⟩  := B1 A x B h3
      exact mark

--(7.1) Plane separation. Let `l` be a line.
--The set of points not lying on `l` can be partitioned into two nonempty
--subsets `S₁` and `S₂` satisfying the following property:
--points `A, B` not in `l`, belong to the same set (`S₁` or `S₂`) iff
--`Seg A B` does not intersect `l`


lemma Prop7_1 (l:Set Point) (_ : Line l) : ∃ S₁ S₂ : Set Point,
  (∃x, x∈S₁) ∧ (∃x, x∈S₂) ∧ S₁∩S₂=∅ ∧ S₁∪S₂ = univ \ l ∧
  (∀ A B:Point, A∉l → B∉l →
    ((A∈S₁ ∧ B∈S₁) ∨ (A∈S₂ ∧ B∈S₂) ↔ Seg A B ∩ l = ∅))
  := by
--Put `R` as the relation A∼B iff A=B or `Seg A B` does not meet `l`.
let R(A B:Point):Prop:=A=B∨∀ᵉx∈ Seg A B, x∉l
--`R` is an equivalence relation on the set of all points not lying on `l`.
--First, it is reflexive.
have R_refl : ∀ A:Point, A∉l→ R A A :=
by intro A _; dsimp; left; rfl
--Second, it is symmetric.
have R_symm : ∀A B:Point, A∉l→B∉l→
  R A B → R B A := by
  intro A B _ _ hR; obtain (hR | hR) := hR
  · left;  symm; exact hR
  · right; rw [← Note7_1 A B]; exact hR
--Third, it is transitive.
have R_trans : ∀ A B C:Point, A∉l→B∉l→C∉l→ R A B → R B C → R A C := by
  --Let `A∼B` and `B∼C`.
  intro A B C _ _ _ hAB hBC
  --Ultimately, we need only consider the case `A,B,C` are distinct.
  obtain (h|_) := em (A=B)
  rw [h]; assumption
  obtain (h|_) := em (A=C)
  rw [h]; apply R_refl; assumption
  obtain (h|_) := em (B=C)
  rw [← h]; assumption
  --Our goal is to show `A∼C`. We split into cases.

------------------------------
  --We show this holds if `A, B, C` are not colinear.
  have Case_2 (A B C : Point) (_:A≠B) (_:A≠C) (_:B≠C)
    (_:A∉l) (_:B∉l) (_:C∉l) (hAB:R A B) (hBC: R B C):
      ¬Colinear A B C → R A C := by
    intro hcol
    --Since `A~B`, `l` does not meet `Seg A B`.
    --Since `B~C`, `l` does not meet `Seg B C`.
    obtain (_|hlAB) := hAB; contradiction
    obtain (_|hlBC) := hBC; contradiction
    --Now by `B4`, it follows `l` does not meet `Seg A C`. Hence `A∼C`.
    right; intro D hD hDl
    obtain (⟨⟨D₁,_,_⟩,_⟩ | ⟨_,⟨D₂,_,_⟩⟩) := B4 A B C (by assumption)
      (by assumption) hcol (by assumption)
      (by assumption) (by assumption)
      (by
        use D
        constructor; assumption
        unfold Seg at hD; dsimp at hD
        obtain (hD|hD|hD) := hD
        · rw [hD] at hDl; contradiction
        · rw [hD] at hDl; contradiction
        · obtain ⟨_,_,_,_,_⟩ := B1 C D A hD; assumption
        )

    · apply hlAB D₁
      unfold Seg; dsimp; right; right
      obtain ⟨_,_,_,_,_⟩ := B1 A D₁ B (by assumption)
      assumption; assumption

    · apply hlBC D₂
      unfold Seg; dsimp; right; right
      obtain ⟨_,_,_,_,_⟩ := B1 B D₂ C (by assumption)
      assumption; assumption



  obtain (⟨m,_, h, _, _⟩ | hcol) := em (Colinear A B C)
  · --Case 1: suppose `A, B, C` are colinear, lying on line `m`.
    --Since `A, B, C` do not lie on `l`, we have `m≠l`.
    have h : m≠l := by
      intro heq; rw [heq] at h; contradiction
    --By `Prop6_1`, `l` and `m` can meet in at most one point.
    have h := Prop6_1 m (by assumption) l (by assumption) h
    --But by `I2` every line has at least two points.
    obtain ⟨D₁, D₂, _, _, _⟩ := I2 l (by assumption)
    --Therefore there exists a point `D∈l` such that `D∉m`,
    --namely either `D₁` or `D₂`.
    have h1 : ∃D, D∈l ∧ D∉m := by
      obtain (_|_) := em (D₁∈m)
      · use D₂; constructor; assumption
        intro; apply h
        use D₁, D₂
      · use D₁

    obtain ⟨D, h1, _⟩ := h1
    --Now apply `B2` to find a point `E` such that `Between D A E`.
    have _ : D≠A := by
      intro h2
      rw [h2] at h1
      contradiction
    obtain ⟨E,_⟩ := B2 D A (by assumption)

    --Then `D,A,E` are collinear (`B1`).
    --Hence `E` is not on `l`, since `A` is not on `l`,
    --and the line `DAE` already meets at the point `D`.
    obtain ⟨_,_, _, _, hcolDAE⟩ := B1 D A E (by assumption)
    have _ : E∉l := by
      intro
      have : A∈l := by
        obtain ⟨n, _, _, _, _⟩ := hcolDAE
        obtain ⟨o,⟨⟨_,_,_⟩,ho⟩⟩ := I1 D E (by assumption)
        have this := ho n
          (by
            constructor; assumption; constructor
            assumption; assumption
          )
        have that := ho l
          (by
            constructor; assumption; constructor
            assumption; assumption
          )
        rw [that, ← this]; assumption

      contradiction

    --Furthermore, `Seg A E` cannot meet `l`; hence `A∼E`.
    --To show this suppose they met at `x`.
    have hAE : R A E := by
      right
      intro x hx1 hx2
      unfold Seg at hx1
      obtain (hx1|hx1|hx1) := hx1
      rw [hx1] at hx2; contradiction
      rw [hx1] at hx2; contradiction

      --Then `x=D`.
      --To prove this observe `x,E,D,A` lie on the same line.
      obtain ⟨_,_, _, _, ⟨n, _, _, _, _⟩⟩ := B1 E x A (by assumption)
      obtain ⟨_,_, _, _, ⟨o, _, _, _, _⟩⟩ := B1 E A D (by assumption)
      have hno : n=o := by
        obtain ⟨p,⟨⟨_,_,_⟩,hp⟩⟩ := I1 E A (by assumption)
        have this := hp n
          (by
            constructor; assumption; constructor
            assumption; assumption
          )
        have that := hp o
            (by
            constructor; assumption; constructor
            assumption; assumption
          )
        rw [that, ← this]

      --This line cannot be `l`.
      have : l≠o := by
        intro hlo
        have : E∈l := by rw [hlo]; assumption
        contradiction

      --So if `x≠D`, then by uniquness `l=o`, a contradiction.
      obtain (_|_) := em (x≠D)
      obtain ⟨p,⟨⟨_,_,_⟩,hp⟩⟩ := I1 x D (by assumption)
      have this := hp l
          (by
            constructor; assumption; constructor
            assumption; assumption
          )
      have that := hp o
        (by
          constructor; assumption; constructor
          rw[← hno]; assumption; assumption
        )
      rw [← that] at this; contradiction

      --Thus `x=D` contradicting `B3`.
      have : x=D := by by_contra; contradiction
      rw [this] at hx1
      have : D ≠ A ∧ D ≠ E ∧ A ≠ E ∧ D ∈ o ∧ A ∈ o ∧ E ∈ o := by

        constructor; assumption; constructor; assumption
        constructor; assumption; constructor; assumption
        constructor; assumption; assumption

      obtain(⟨_,_,_⟩|⟨_,_,_⟩|⟨_,_,_⟩) := B3 D A E o (by assumption) this
      · contradiction
      · contradiction
      · contradiction
    -- Note also that `E` does not lie on `m`
    have that : E ∉ m := by
      intro h
      obtain ⟨lDA, _, h, _, _⟩ := hcolDAE
      obtain ⟨p,⟨⟨_,_,_⟩,hp⟩⟩ := I1 A E (by assumption)
      have this := hp m
          (by
            constructor; assumption; constructor
            assumption; assumption
          )
      have that := hp lDA
        (by
          constructor; assumption; constructor
          assumption; assumption
        )
      rw [← that] at this
      rw [← this] at h
      contradiction

    --We claim `A,B,E` are non colinear points.
    have hcolABE : ¬Colinear A B E := by
      rintro ⟨n,_,_,_,_⟩
      have : n=m := by
        obtain ⟨p,⟨⟨_,_,_⟩,hp⟩⟩ := I1 A B (by assumption)
        have this := hp n
            (by
              constructor; assumption; constructor
              assumption; assumption
            )
        have that := hp m
          (by
            constructor; assumption; constructor
            assumption; assumption
          )
        rw [← that] at this; assumption


      rw [← this] at that
      contradiction





    -- Applying `Case_2`, `A~E` and `A~B` implies `B~E`.
    have := Case_2 B A E (by symm; assumption)
      (by
        intro h
        rw [← h] at that
        contradiction)
      (by assumption)
      (by assumption) (by assumption) (by assumption)
      (by apply R_symm A B; assumption; assumption; assumption)
      (by assumption)
      (by
        rintro ⟨p, _, _, _, _⟩
        apply hcolABE
        use p)

    --Then again, `B~E` and `B~C` implies `C~E`.
    have := Case_2 C B E (by symm; assumption)
      (by
        intro h
        rw [← h] at that
        contradiction)
      (by
        intro h
        rw [← h] at that
        contradiction)
      (by assumption) (by assumption) (by assumption)
      (by apply R_symm B C; assumption; assumption; assumption)
      (by assumption)
      (by
        rintro ⟨q, _, _, _, _⟩
        apply that
        obtain ⟨p,⟨⟨_,_,_⟩,hp⟩⟩ := I1 B C (by assumption)
        have this := hp m
            (by
              constructor; assumption; constructor
              assumption; assumption
            )
        have that := hp q
          (by
            constructor; assumption; constructor
            assumption; assumption
          )
        rw [this, ←that]; assumption)


    --Finally once more, `A~E` and `C~E` implies `A~C`.
    apply Case_2 A E C (by assumption) (by assumption)
      (by
        intro h
        rw [h] at that
        contradiction)
      (by assumption)
      (by assumption)
      (by assumption)

    assumption
    apply R_symm C E (by assumption) (by assumption)
    assumption

    rintro ⟨q, _, _, _, _⟩
    apply that
    obtain ⟨p,⟨⟨_,_,_⟩,hp⟩⟩ := I1 A C (by assumption)
    have this := hp m
        (by
          constructor; assumption; constructor
          assumption; assumption
        )
    have that := hp q
      (by
        constructor; assumption; constructor
        assumption; assumption
      )
    rw [this, ←that]; assumption




  · --Case 2: already solved.
    apply Case_2 A B C
    repeat {assumption}

-----------Done with trans---------

--Next, `axiom I3` (`SudI2`) implies that there are points `P₁∈l` and `A∉l`.
--So let `S₁` be the equivalence class of `A`.
obtain ⟨_, P₁, A, hA, _, _, _, _, hP1⟩ := SudI2 l (by assumption)
use {P | P∉l ∧ R A P}

--And, `axiom B2` implies there is a point `C` such that `Between A P₁ C`.
--So let `S₂` be the equivalence class of `C`.
obtain ⟨C, hC⟩ := B2 A P₁ (by exact id (Ne.symm hP1))
use {P | P∉l ∧ R P C}

--We claim `S₁` and `S₂` are the only two equivalence classes.

--First, `S₁` is nonempty since `A∼A`.
constructor
· use A; exact ⟨hA, by apply R_refl; assumption⟩

--Second, `C∉l` which implies `S₂` is nonempty since `C∼C`.
--For if `C∈l` then `Between A P₁ C` implies `A∈l`, a contradiction
have _ : C∉l := by
  intro hC
  apply hA
  obtain ⟨_, _, _, _, l₂, _, _, _, _⟩ := B1 A P₁ C (by assumption)
  obtain ⟨l₃, _, hunq⟩ := I1 P₁ C (by assumption)
  have this := hunq l ⟨by assumption, by assumption, by assumption⟩
  have that := hunq l₂ ⟨by assumption, by assumption, by assumption⟩
  rw[this, ← that]
  assumption
constructor
· use C; exact ⟨by assumption, by apply R_refl; assumption⟩

--It helps to take a detour and prove `A+C`.
have hAC : ¬ R A C := by
--Assume `R A C`
  rintro (h3 | h3)
  · --Case 1: supose `A=C`. Since `Between A P₁ C`,
    --the points must be distinct, a contrdiction.
    obtain ⟨_, _, _⟩ := B1 A P₁ C (by assumption)
    contradiction

  · --Case 2: suppose `Seg A C` does not meet `l`.
    --But `P₁ ∈ Seg A C` lies in `l`, a contradiction.
    apply h3 P₁
    unfold Seg; dsimp; right; right
    obtain ⟨_, _, _, _, _⟩ := B1 A P₁ C (by assumption)
    assumption; assumption

--Third, we show `S₁∩S₂=∅`.
have Sint : {P | ¬P ∈ l ∧ R A P} ∩ {P | ¬P ∈ l ∧ R P C} = ∅ := by
  --We prove `B ∈ S₁∩S₂` iff `B ∈ ∅`.
  ext B
  constructor

  · -- (=>) let `B ∈ S₁∩S₂` so that `A∼B` and `B∼C`.
    rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    -- Since `A≁C`, trans gives a desired contra.
    apply hAC; apply R_trans A B C; repeat {assumption}

  · -- (<=) Trivial
    intro; contradiction

constructor; exact Sint

-- Fourth, we show `S₁∪S₂` equals the set of all points without `l`.
have Sun : {P | ¬P ∈ l ∧ R A P} ∪ {P | ¬P ∈ l ∧ R P C} = univ \ l := by
  --We prove `B ∈ S₁∪S₂` iff `B ∈ univ \ l`.
  ext B
  constructor

  · -- (=>) Trivial
    rintro (⟨h,_⟩ | ⟨h,_⟩)
    repeat {exact mem_diff_of_mem trivial h}

  · -- (<=) Let `B∉l`.
    rintro ⟨_, _⟩
    --It suffices to show `B≁C` implies `A∼B`.
    suffices h: ¬R B C→ R A B
    obtain (hBC | hBC) := em (R B C)
    · -- In case `R B C`, then `B∈S₂`.
      right; constructor; repeat assumption

    · --So suppose `¬R B C`. We ultimately argue `A∈S₁`.
      left; constructor; assumption; exact h hBC
    intro hBC
    --Our goal is to prove `R A B`
    --The only case we are left to consider is when `A,B,C` are distinct.
    have : A≠C := by
      obtain ⟨_, _, _⟩ := B1 A P₁ C hC; assumption
    obtain (_ | _) := em (A=B)
    left; assumption

    have : B≠C := by
      intro; apply hBC; left; assumption

    --We break into two cases.
    --------------------
    have Case_2 (A B C : Point) (_:A≠B) (_:A≠C) (_:B≠C)
    (_:A∉l) (_:B∉l) (_:C∉l) (hAB:R A B) (hBC: R B C):
      ¬Colinear A B C → R A C := by
      intro hcol
      --Since `A~B`, `l` does not meet `Seg A B`.
      --Since `B~C`, `l` does not meet `Seg B C`.
      obtain (_|hlAB) := hAB; contradiction
      obtain (_|hlBC) := hBC; contradiction
      --Now by `B4`, it follows `l` does not meet `Seg A C`. Hence `A∼C`.
      right; intro D hD hDl
      obtain (⟨⟨D₁,_,_⟩,_⟩ | ⟨_,⟨D₂,_,_⟩⟩) := B4 A B C (by assumption)
        (by assumption) hcol (by assumption)
        (by assumption) (by assumption)
        (by
          use D
          constructor; assumption
          unfold Seg at hD; dsimp at hD
          obtain (hD|hD|hD) := hD
          · rw [hD] at hDl; contradiction
          · rw [hD] at hDl; contradiction
          · obtain ⟨_,_,_,_,_⟩ := B1 C D A hD; assumption
          )

      · apply hlAB D₁
        unfold Seg; dsimp; right; right
        obtain ⟨_,_,_,_,_⟩ := B1 A D₁ B (by assumption)
        assumption; assumption

      · apply hlBC D₂
        unfold Seg; dsimp; right; right
        obtain ⟨_,_,_,_,_⟩ := B1 B D₂ C (by assumption)
        assumption; assumption

    obtain (hcol | hcol) := em (Colinear A B C)
    · --Case 1: suppose `A,B,C` are colinear, lying on a line `m`.
      unfold Colinear at hcol; obtain ⟨m, _, h, _, _⟩ := hcol
      ----AS IN CASE 1 FROM BEFORE-------
      have h : m≠l := by
        intro heq; rw [heq] at h; contradiction
      --By `Prop6_1`, `l` and `m` can meet in at most one point.
      have h := Prop6_1 m (by assumption) l (by assumption) h
      --But by `I2` every line has at least two points.
      obtain ⟨D₁, D₂, _, _, _⟩ := I2 l (by assumption)
      --Therefore there exists a point `D∈l` such that `D∉m`,
      --namely either `D₁` or `D₂`.
      have h1 : ∃D, D∈l ∧ D∉m := by
        obtain (_|_) := em (D₁∈m)
        · use D₂; constructor; assumption
          intro; apply h
          use D₁, D₂
        · use D₁

      obtain ⟨D, h1, _⟩ := h1
      --Now apply `B2` to find a point `E` such that `Between D A E`.
      have _ : D≠A := by
        intro h2
        rw [h2] at h1
        contradiction
      obtain ⟨E,_⟩ := B2 D A (by assumption)
      --Then `D,A,E` are collinear (`B1`).
      --Hence `E` is not on `l`, since `A` is not on `l`,
      --and the line `DAE` already meets at the point `D`.
      obtain ⟨_,_, _, _, hcolDAE⟩ := B1 D A E (by assumption)
      have _ : E∉l := by
        intro
        have : A∈l := by
          obtain ⟨n, _, _, _, _⟩ := hcolDAE
          obtain ⟨o,⟨⟨_,_,_⟩,ho⟩⟩ := I1 D E (by assumption)
          have this := ho n
            (by
              constructor; assumption; constructor
              assumption; assumption
            )
          have that := ho l
            (by
              constructor; assumption; constructor
              assumption; assumption
            )
          rw [that, ← this]; assumption

        contradiction

      --Furthermore, `Seg A E` cannot meet `l`; hence `A∼E`.
      --To show this suppose they met at `x`.
      have hAE : R A E := by
        right
        intro x hx1 hx2
        unfold Seg at hx1
        obtain (hx1|hx1|hx1) := hx1
        rw [hx1] at hx2; contradiction
        rw [hx1] at hx2; contradiction
        --Then `x=D`.
        --To prove this observe `x,E,D,A` lie on the same line.
        obtain ⟨_,_, _, _, ⟨n, _, _, _, _⟩⟩ := B1 E x A (by assumption)
        obtain ⟨_,_, _, _, ⟨o, _, _, _, _⟩⟩ := B1 E A D (by assumption)
        have hno : n=o := by
          obtain ⟨p,⟨⟨_,_,_⟩,hp⟩⟩ := I1 E A (by assumption)
          have this := hp n
            (by
              constructor; assumption; constructor
              assumption; assumption
            )
          have that := hp o
              (by
              constructor; assumption; constructor
              assumption; assumption
            )
          rw [that, ← this]

        --This line cannot be `l`.
        have : l≠o := by
          intro hlo
          have : E∈l := by rw [hlo]; assumption
          contradiction

        --So if `x≠D`, then by uniquness `l=o`, a contradiction.
        obtain (_|_) := em (x≠D)
        obtain ⟨p,⟨⟨_,_,_⟩,hp⟩⟩ := I1 x D (by assumption)
        have this := hp l
            (by
              constructor; assumption; constructor
              assumption; assumption
            )
        have that := hp o
          (by
            constructor; assumption; constructor
            rw[← hno]; assumption; assumption
          )
        rw [← that] at this; contradiction

        --Thus `x=D` contradicting `B3`.
        have : x=D := by by_contra; contradiction
        rw [this] at hx1
        have : D ≠ A ∧ D ≠ E ∧ A ≠ E ∧ D ∈ o ∧ A ∈ o ∧ E ∈ o := by

          constructor; assumption; constructor; assumption
          constructor; assumption; constructor; assumption
          constructor; assumption; assumption

        obtain(⟨_,_,_⟩|⟨_,_,_⟩|⟨_,_,_⟩) := B3 D A E o (by assumption) this
        · contradiction
        · contradiction
        · contradiction
      ------------------------------------------

      have hCE: ¬ R C E := by
        intro hCE
        apply hAC
        have := R_symm C E (by assumption) (by assumption) (by assumption)
        apply R_trans A E C
        repeat {assumption}

      have hEC : ¬ R E C := by
        intro; apply hCE; apply R_symm E C; repeat {assumption}


      have hcolBCE : ¬Colinear B C E := by
        intro hcol; unfold Colinear at hcol;
        obtain ⟨p,_,_,_,h⟩ := hcol
        have : m=p := by
          obtain ⟨q,⟨⟨_,_,_⟩,hq⟩⟩ := I1 B C (by assumption)
          have this := hq m
              (by
                constructor; assumption; constructor
                assumption; assumption
              )
          have that := hq p
            (by
              constructor; assumption; constructor
              assumption; assumption
            )
          rw [that, this]
        rw [← this] at h
        suffices: D∈m; contradiction
        obtain ⟨s,_,_, _, _⟩ := hcolDAE;
        suffices h : m=s; rw [h]; assumption
        obtain ⟨q,⟨⟨_,_,_⟩,hq⟩⟩ := I1 A E (by assumption)
        have this := hq m
            (by
              constructor; assumption; constructor
              assumption; assumption
            )
        have that := hq s
          (by
            constructor; assumption; constructor
            assumption; assumption
          )
        rw [that, this]

      suffices : R B E; apply R_trans A E B; repeat {assumption}
      apply R_symm B E; repeat {assumption}

      have hcol : ¬Colinear B E C := by
        rintro ⟨p,_,_,_,_⟩; apply hcolBCE; use p


      ---adopt next case to BCE
      push_neg at hBC; dsimp at hBC; push_neg at hBC
      obtain ⟨_, x, hx, hxl⟩ := hBC

      push_neg at hEC; dsimp at hEC; push_neg at hEC
      obtain ⟨_, y, hy, hyl⟩ := hEC

      right; intro D' _ _
      obtain (⟨_,hn⟩|⟨hn,_⟩) := B4 B E C l (by assumption) hcol
        (by assumption) (by assumption) (by assumption)
        (by
          use x; constructor; assumption
          unfold Seg at hx hy; dsimp at hx hy
          obtain (hx|hx|hx) := hx
          rw [hx] at hxl; contradiction; rw [hx] at hxl; contradiction
          obtain ⟨_,_,_,_,_⟩ := B1 C x B hx
          assumption )


      · apply hn
        use y
        constructor; assumption; unfold Seg at hy; dsimp at hy
        obtain (hf|hf|hf) := hy
        · rw [hf] at hyl; contradiction
        · rw [hf] at hyl; contradiction
        · obtain ⟨_, _, _, _, _⟩ := B1 C y E hf
          assumption
      · apply hn
        use x
        constructor; assumption; unfold Seg at hx; dsimp at hx
        obtain (hf|hf|hf) := hx
        · rw [hf] at hxl; contradiction
        · rw [hf] at hxl; contradiction
        · obtain ⟨_, _, _, _, _⟩ := B1 C x B hf
          assumption



    · --Case 2: suppose `A,B,C` are not colinear.
      -- From `A+C` we conclude that `Seg A C` meets `l` (say at `x`).
      push_neg at hAC; dsimp at hAC; push_neg at hAC
      obtain ⟨_, x, hx, hxl⟩ := hAC
      -- From `B+C` we conclude that `Seg B C` meets `l` (say at `y`).
      push_neg at hBC; dsimp at hBC; push_neg at hBC
      obtain ⟨_, y, hy, hyl⟩ := hBC
      -- Now by Pasch's axiom (B4) it follows that
      -- `Seg A B` does not meet `l`, so `A~B` as required.
      right; intro D _ _
      obtain (⟨_,hn⟩|⟨hn,_⟩) := B4 A B C l (by assumption) hcol
        (by assumption) (by assumption) (by assumption) (by use P₁)
      · apply hn
        use y
        constructor; assumption; unfold Seg at hy; dsimp at hy
        obtain (hf|hf|hf) := hy
        · rw [hf] at hyl; contradiction
        · rw [hf] at hyl; contradiction
        · obtain ⟨_, _, _, _, _⟩ := B1 C y B hf
          assumption
      · apply hn
        use x
        constructor; assumption; unfold Seg at hx; dsimp at hx
        obtain (hf|hf|hf) := hx
        · rw [hf] at hxl; contradiction
        · rw [hf] at hxl; contradiction
        · obtain ⟨_, _, _, _, _⟩ := B1 C x A hf
          assumption

constructor; exact Sun


-- Finally we show points `x, y ∉ l` belong to the same set
--(`S₁` or `S₂`) iff `Seg x y` does not intersect `l`.
intro x y hx _
constructor
· -- (=>) If `x=y`, then we are done.
  obtain (heq | heq) := em (x=y)
  -- For in that case, we show `Seg x y ∩ l = ∅`.
  intro; ext B; constructor
  intro h; obtain ⟨h,hB⟩ := h
  rw [← heq] at h
  unfold Seg at h; dsimp at h
  obtain (h | h | h) := h
  rw [h] at hB; contradiction
  rw [h] at hB; contradiction
  obtain ⟨_,_, _⟩ := B1 x B x h
  contradiction
  intro; contradiction
  --So suppose `x≠y`. Then we show `Seg x y ∩ l = ∅`.
  rintro (⟨⟨_,hAx⟩,⟨_,hAy⟩⟩ | ⟨⟨_,hxC⟩,⟨_,hyC⟩⟩)
  · ext B; constructor; rintro ⟨_,_⟩
    have hxA := R_symm A x (by assumption) (by assumption) hAx
    have hxy := R_trans x A y (by assumption) (by assumption)
      (by assumption) hxA hAy
    obtain (_|h) := hxy; contradiction
    specialize h B (by assumption)
    contradiction
    intro; contradiction

  · ext B; constructor; rintro ⟨_,_⟩
    have hCy := R_symm y C (by assumption) (by assumption) hyC
    have hxy := R_trans x C y (by assumption) (by assumption)
      (by assumption) hxC hCy
    obtain (_|h) := hxy; contradiction
    specialize h B (by assumption)
    contradiction
    intro; contradiction

· -- (<=) Suppose `Seg x y ∩ l = ∅`.
  intro h

  have hxy : R x y := by
    right
    intro B h1 h2
    have : B ∈ Seg x y ∩ l := mem_inter h1 h2
    rw [h] at this
    contradiction

  have : x ∈ univ \ l :=  mem_diff_of_mem trivial hx
  rw [← Sun] at this
  obtain (⟨_,_⟩ | ⟨_,_⟩) := this

  · left; constructor; constructor; assumption; assumption
    constructor; assumption
    apply R_trans A x y; assumption; assumption; assumption
    assumption; assumption

  · right; constructor; constructor; assumption; assumption
    constructor; assumption
    apply R_trans y x C; assumption; assumption; assumption
    apply R_symm; assumption; assumption; assumption; assumption



--We wish to call `S₁` and `S₂` the "two sides of `l`".
--Here is how we formalize this deifniton in Lean.
--For any set of points `S`, we think of  `Side S l` as the proposition
--which is true when `S` consists of points not lying on `l`,
--but lying on one "side" of `l`.

def Side (S l: Set Point) : Prop := ∃x, x∈S ∧ 
  ∀A, A∈S ↔ Seg x A ∩ l = ∅

--While `Side S l` does not require `l` a line, anytime we use it
-- the context has a proof `l` is a line.

