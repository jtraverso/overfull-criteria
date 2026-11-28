module

public import OverfullWork.ChenShanPackedSpecialPaths
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset DirectedRobustExpansion
open scoped Classical

/-- Position in a canonical closed interval of the cluster cycle.
At offset t the index is the next interval's initial cluster. -/
def canonicalSpecialPosition {f t : ℕ} (hf : 0 < f) (ht : 0 < t)
    (b : Fin f) (i : ℕ) : Fin (f*t) :=
  ⟨(b.val*t+i) % (f*t), Nat.mod_lt _ (Nat.mul_pos hf ht)⟩

theorem canonicalSpecialPosition_of_lt {f t : ℕ} (hf : 0 < f) (ht : 0 < t)
    (b : Fin f) (i : Fin t) :
    canonicalSpecialPosition hf ht b i.val = finProdFinEquiv (b,i) := by
  apply Fin.ext
  have hBound : b.val*t+i.val < f*t := by
    have h := (Nat.mul_le_mul_right t (Nat.succ_le_of_lt b.isLt))
    rw [Nat.succ_mul] at h
    omega
  change (b.val*t+i.val) % (f*t) = i.val+t*b.val
  rw [Nat.mod_eq_of_lt hBound]
  ac_rfl

private theorem finRotate_val_mod {m : ℕ} (x : Fin m) :
    (finRotate m x).val = (x.val+1) % m := by
  have := x.neZero
  rw [finRotate_apply, Fin.val_add]
  change (x.val + 1 % m) % m = _
  exact Nat.add_mod_mod _ _ _

/-- The last cluster of one interval is the first of the next. -/
theorem canonicalSpecialPosition_terminal {f t : ℕ} (hf : 0 < f) (ht : 0 < t)
    (b : Fin f) :
    canonicalSpecialPosition hf ht b t = canonicalSpecialPosition hf ht (finRotate f b) 0 := by
  apply Fin.ext
  change (b.val*t+t) % (f*t) = ((finRotate f b).val*t+0) % (f*t)
  rw [finRotate_val_mod, add_zero, ← Nat.succ_mul, Nat.mul_mod_mul_right,
    Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ hf) ht)]

theorem canonicalSpecialPosition_succ {f t : ℕ} (hf : 0 < f) (ht : 0 < t)
    (b : Fin f) (i : ℕ) :
    canonicalSpecialPosition hf ht b (i+1) = finRotate (f*t) (canonicalSpecialPosition hf ht b i) := by
  apply Fin.ext
  rw [finRotate_val_mod]
  change (b.val*t+(i+1)) % (f*t) = ((b.val*t+i) % (f*t)+1) % (f*t)
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem canonicalSpecialPosition_injOn {f t : ℕ} (hf : 2 ≤ f) (ht : 0 < t)
    (b : Fin f) {i j : ℕ} (hi : i ≤ t) (hj : j ≤ t)
    (h : canonicalSpecialPosition (by omega) ht b i =
      canonicalSpecialPosition (by omega) ht b j) : i = j := by
  have hStrict : t < f*t := by
    have h := Nat.mul_le_mul_right t hf
    omega
  have hmod : b.val*t+i ≡ b.val*t+j [MOD f*t] := congrArg Fin.val h
  rcases le_total i j with hle | hle
  · have hDiv := (Nat.modEq_iff_dvd' (by omega : b.val*t+i ≤ b.val*t+j)).mp hmod
    have hEq : b.val*t+j - (b.val*t+i) = j-i := by omega
    rw [hEq] at hDiv
    by_contra hn
    have hSmall := Nat.le_of_dvd (by omega : 0 < j-i) hDiv
    omega
  · have hDiv := (Nat.modEq_iff_dvd' (by omega : b.val*t+j ≤ b.val*t+i)).mp hmod.symm
    have hEq : b.val*t+i - (b.val*t+j) = i-j := by omega
    rw [hEq] at hDiv
    by_contra hn
    have hSmall := Nat.le_of_dvd (by omega : 0 < i-j) hDiv
    omega

private theorem finRotate_no_reverse {m : ℕ} (hm : 3 ≤ m) (x : Fin m) :
    finRotate m (finRotate m x) ≠ x := by
  intro h
  have he := congrArg Fin.val h
  rw [finRotate_val_mod, finRotate_val_mod, Nat.mod_add_mod] at he
  have hmod : x.val ≡ x.val+2 [MOD m] := by
    change x.val % m = (x.val+2)%m
    rw [Nat.mod_eq_of_lt x.isLt]
    simpa only [Nat.add_assoc] using he.symm
  have hD := (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).mp hmod
  have hSmall := Nat.le_of_dvd (by omega : 0 < x.val+2-x.val) hD
  omega

variable {V : Type*}

/-- The subcluster at a position of a special interval. The first
component of b indexes the refinement class, and the second the
interval on the cluster cycle. -/
def canonicalSpecialCluster {h f t : ℕ} (hf : 0 < f) (ht : 0 < t)
    (C : Fin h × Fin (f*t) → Finset V) (b : Fin h × Fin f) (i : ℕ) : Finset V :=
  C (b.1, canonicalSpecialPosition hf ht b.2 i)

/-- Transition sources and targets both enumerate the subclusters
exactly once. This includes the cyclic wrap at the shared boundary. -/
theorem canonicalSpecial_transition_equivalences {h f t : ℕ} (hf : 0 < f) (ht : 0 < t) :
    let source (p : (Fin h × Fin f) × Fin t) :=
      (p.1.1, canonicalSpecialPosition hf ht p.1.2 p.2.val)
    let target (p : (Fin h × Fin f) × Fin t) :=
      (p.1.1, canonicalSpecialPosition hf ht p.1.2 (p.2.val+1))
    Function.Bijective source ∧ Function.Bijective target := by
  intro source target
  let e : (Fin h × Fin f) × Fin t ≃ Fin h × Fin (f*t) :=
    (Equiv.prodAssoc _ _ _).trans ((Equiv.refl _).prodCongr finProdFinEquiv)
  have hSource : source = e := by
    funext p
    exact Prod.ext rfl (canonicalSpecialPosition_of_lt hf ht p.1.2 p.2)
  have hTarget : target = e.trans ((Equiv.refl _).prodCongr (finRotate (f*t))) := by
    funext p
    change (p.1.1, canonicalSpecialPosition hf ht p.1.2 (p.2.val+1)) =
      (p.1.1, finRotate (f*t) ((e p).2))
    rw [canonicalSpecialPosition_succ, ← hSource]
  rw [hSource, hTarget]
  exact ⟨e.bijective, (e.trans ((Equiv.refl _).prodCongr (finRotate (f*t)))).bijective⟩

/-- The subdivision of the cycle supplies all incidence and
separation hypotheses of the filling and factor constructions. -/
theorem canonicalSpecial_interval_geometry {h f t : ℕ}
    (hf : 2 ≤ f) (ht : 0 < t) (hCycle : 3 ≤ f*t)
    (C : Fin h × Fin (f*t) → Finset V) (core : Finset V)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hSub : ∀ i, C i ⊆ core) (hCover : ∀ v ∈ core, ∃ i, v ∈ C i) :
    let A := canonicalSpecialCluster (by omega : 0 < f) ht C
    (∀ b i, i ≤ t → A b i ⊆ core) ∧
    (∀ b i j, i ≤ t → j ≤ t → i ≠ j → Disjoint (A b i) (A b j)) ∧
    (∀ p q : (Fin h × Fin f) × Fin t, p ≠ q →
      Disjoint (A p.1 p.2.val) (A q.1 q.2.val)) ∧
    (∀ p q : (Fin h × Fin f) × Fin t,
      Disjoint (A p.1 p.2.val) (A q.1 (q.2.val+1)) ∨
      Disjoint (A p.1 (p.2.val+1)) (A q.1 q.2.val)) ∧
    (∀ v ∈ core, ∃! p : (Fin h × Fin f) × Fin t, v ∈ A p.1 p.2.val) ∧
    (∀ v ∈ core, ∃! p : (Fin h × Fin f) × Fin t, v ∈ A p.1 (p.2.val+1)) := by
  intro A
  have hf' : 0 < f := by omega
  let source (p : (Fin h × Fin f) × Fin t) :=
    (p.1.1, canonicalSpecialPosition hf' ht p.1.2 p.2.val)
  let target (p : (Fin h × Fin f) × Fin t) :=
    (p.1.1, canonicalSpecialPosition hf' ht p.1.2 (p.2.val+1))
  obtain ⟨hSource, hTarget⟩ := canonicalSpecial_transition_equivalences (h := h) hf' ht
  have hUnique (φ : (Fin h × Fin f) × Fin t → Fin h × Fin (f*t))
      (hφ : Function.Bijective φ) (v : V) (hv : v ∈ core) :
      ∃! p, v ∈ C (φ p) := by
    obtain ⟨i, hi⟩ := hCover v hv
    obtain ⟨p, hp⟩ := hφ.2 i
    have hp' : v ∈ C (φ p) := by rwa [hp]
    refine ⟨p, hp', fun q hq => hφ.1 ?_⟩
    by_contra hn
    exact disjoint_left.mp (hC hn) hq hp'
  refine ⟨fun b i _ => hSub _, ?_, ?_, ?_, hUnique source hSource, hUnique target hTarget⟩
  · intro b i j hi hj hne
    apply hC
    intro he
    exact hne (canonicalSpecialPosition_injOn hf ht b.2 hi hj (congrArg Prod.snd he))
  · intro p q hn
    exact hC (fun hEq => hn (hSource.1 hEq))
  · intro p q
    change Disjoint (C (source p)) (C (target q)) ∨ Disjoint (C (target p)) (C (source q))
    by_cases he : source p = target q
    · right
      apply hC
      intro he'
      have h1 := congrArg Prod.snd he
      have h2 := congrArg Prod.snd he'
      change canonicalSpecialPosition hf' ht p.1.2 p.2.val =
        canonicalSpecialPosition hf' ht q.1.2 (q.2.val+1) at h1
      change canonicalSpecialPosition hf' ht p.1.2 (p.2.val+1) =
        canonicalSpecialPosition hf' ht q.1.2 q.2.val at h2
      rw [canonicalSpecialPosition_succ] at h1 h2
      exact finRotate_no_reverse hCycle _ ((congrArg (finRotate (f*t)) h2).trans h1.symm)
    · exact Or.inl (hC he)

/-- Construct all factors for one family of canonical intervals from
the occupied sets and the quantitative filling margins. Use h=1
for the coarse family and h equal to the refinement size for the
fine family. -/
theorem exists_canonical_special_factors [Fintype V] {h f t s : ℕ}
    (hf : 2 ≤ f) (ht : 0 < t) (hCycle : 3 ≤ f*t)
    (C : Fin h × Fin (f*t) → Finset V) (core : Finset V) (G : Digraph V)
    (U W : (Fin h × Fin f) → Fin s → ℕ → Finset V) (n r b : ℕ) (ε η d a : ℝ)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hSub : ∀ i, C i ⊆ core) (hCover : ∀ v ∈ core, ∃ i, v ∈ C i)
    (hn : 0 < n) (hSize : ∀ i, (C i).card = n)
    (hη : 0 < η) (hηOne : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : (s:ℝ) ≤ a*((n:ℝ)*η))
    (hGap : 2*η < d) (hr : 0 < r) (hCut : (n:ℝ)*η ≤ (r:ℝ))
    (hMargin : (r:ℝ)+(b:ℝ) ≤ (d-η)*(n:ℝ)) :
    let A := canonicalSpecialCluster (by omega : 0 < f) ht C
    (∀ c j i, i < t → U c j i ⊆ A c i) →
    (∀ c j i, i < t → W c j i ⊆ A c (i+1)) →
    (∀ c j i, i < t → (U c j i).card = (W c j i).card ∧ (U c j i).card ≤ b) →
    (∀ c i, i < t → IsLowerSuperregularPair G ε d (A c i) (A c (i+1))) →
    let H (c : Fin h × Fin f) (j : Fin s) : Digraph V :=
      ⟨fun x y => G.Adj x y ∨ ∃ i < t, x ∈ U c j i ∧ y ∈ W c j i⟩
    ∃ P : ∀ c j, OrderedClusterPaths (H c j) (A c) (Fin n) 0 t,
      (∀ c j i, i < t → ∀ k, (P c j).vertex i k ∈ U c j i ↔
        (P c j).vertex (i+1) k ∈ W c j i) ∧
      (∀ j v, v ∈ core → (∃! w, (specialFactorDigraph (fun c => P c j)).Adj v w) ∧
        (∃! w, (specialFactorDigraph (fun c => P c j)).Adj w v)) ∧
      let real (p : ((Fin h × Fin f) × Fin t) × Fin s) :=
        specialPathFillingArcs (P p.1.1 p.2) (U p.1.1 p.2 p.1.2.val) p.1.2.val
      (∀ p, real p ≤ G) ∧
      (∀ p q x y u v, (real p).Adj x y → (real q).Adj u v → s(x,y) = s(u,v) → p = q) := by
  classical
  intro A hU hW hUW hPair H
  obtain ⟨hCore, hDis, hStartsDis, hReverse, hStarts, hEnds⟩ :=
    canonicalSpecial_interval_geometry hf ht hCycle C core hC hSub hCover
  obtain ⟨P, hSteps, _, hReal, _, hNoReuse⟩ := exists_packed_special_path_systems
    G A U W t n r ε η d a hn (fun _ _ _ => hSize _) hDis
    (fun p q hpq => Or.inl (hStartsDis p q hpq))
    hU hW (fun c j i hi => (hUW c j i hi).1) hPair
    hη hηOne ha hd hTol hBudget hGap hr hCut (fun c j i hi => by
      have h := (hUW c j i hi).2
      have hCast : ((U c j i).card:ℝ) ≤ (b:ℝ) := by exact_mod_cast h
      linarith only [hCast, hMargin])
  refine ⟨P, hSteps, ?_, hReal, hNoReuse hReverse⟩
  intro j
  exact (specialFactorDigraph_regular_on_core (fun c => P c j) core hCore hStarts hEnds).2

end OverfullWork.ChenShan
