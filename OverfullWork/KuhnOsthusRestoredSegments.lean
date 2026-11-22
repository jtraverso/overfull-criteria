module

public import OverfullWork.KuhnOsthusMarkedTours
public import OverfullWork.KuhnOsthusCycleAbsorberOriginalArcs

@[expose] public section


/-! Subdivision of exceptional shortcuts preserves the successive
marks on the original cycles, including the order used by the sweeps. -/
namespace OverfullWork.DirectedRobustExpansion

open Function
open scoped Classical
variable {V W M Z : Type*}

def segmentDistance {σ : Equiv.Perm V} {τ : Equiv.Perm W} {mark : V ↪ W}
    (H : MarkedCycleSegments τ mark σ) (x : V) : ℕ → ℕ
  | 0 => 0
  | n+1 => segmentDistance H x n + H.span ((σ : V → V)^[n] x)

theorem segmentDistance_trace {σ : Equiv.Perm V} {τ : Equiv.Perm W} {mark : V ↪ W}
    (H : MarkedCycleSegments τ mark σ) (x : V) (n : ℕ) :
    (τ : W → W)^[segmentDistance H x n] (mark x) = mark ((σ : V → V)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [segmentDistance,Nat.add_comm,iterate_add_apply,ih,H.finish,iterate_succ_apply']

private theorem segmentDistance_coordinates {σ : Equiv.Perm V} {τ : Equiv.Perm W} {mark : V ↪ W}
    (H : MarkedCycleSegments τ mark σ) (x : V) (n d : ℕ) :
    d < segmentDistance H x n ↔
      ∃ i < n, ∃ e < H.span ((σ : V → V)^[i] x), d = segmentDistance H x i + e := by
  induction n with
  | zero => simp [segmentDistance]
  | succ n ih =>
    rw [segmentDistance]
    constructor
    · intro hd
      by_cases h : d < segmentDistance H x n
      · obtain ⟨i,hi,e,he,hde⟩ := ih.mp h
        exact ⟨i,by omega,e,he,hde⟩
      · exact ⟨n,by omega,d-segmentDistance H x n,by omega,by omega⟩
    · rintro ⟨i,hi,e,he,rfl⟩
      by_cases h : i = n
      · subst i
        omega
      · have hlt := ih.mpr ⟨i,by omega,e,he,rfl⟩
        omega

/-- Expand the distances between marks by the lengths of the
underlying subdivided segments. The successor on the marks is unchanged. -/
def MarkedCycleSegments.compose {σ : Equiv.Perm V} {τ : Equiv.Perm W}
    {mark : V ↪ W} {inner : M ↪ V} {next : Equiv.Perm M}
    (H : MarkedCycleSegments τ mark σ) (K : MarkedCycleSegments σ inner next) :
    MarkedCycleSegments τ (inner.trans mark) next where
  span a := segmentDistance H (inner a) (K.span a)
  positive a := by
    have hn := K.positive a
    cases h : K.span a with
    | zero => omega
    | succ n =>
      rw [segmentDistance]
      exact Nat.add_pos_right _ (H.positive _)
  finish a := (segmentDistance_trace H (inner a) (K.span a)).trans (congrArg mark (K.finish a))
  interior a d hd hlt b := by
    obtain ⟨i,hi,e,he,rfl⟩ := (segmentDistance_coordinates H (inner a) (K.span a) d).mp hlt
    change (τ : W → W)^[segmentDistance H (inner a) i+e] (mark (inner a)) ≠ mark (inner b)
    rw [Nat.add_comm,iterate_add_apply,segmentDistance_trace]
    by_cases h : e = 0
    · subst e
      simp only [iterate_zero,id_eq]
      have hip : 0 < i := by
        by_contra! hzero
        have he : i = 0 := by omega
        subst i
        simp [segmentDistance] at hd
      exact fun heq => K.interior a i hip hi b (mark.injective heq)
    · exact H.interior _ _ (Nat.pos_of_ne_zero h) he (inner b)
  covers w := by
    obtain ⟨v,e,he,hw⟩ := H.covers w
    obtain ⟨a,i,hi,rfl⟩ := K.covers v
    refine ⟨a,segmentDistance H (inner a) i+e,
      (segmentDistance_coordinates H (inner a) (K.span a) _).mpr ⟨i,hi,e,he,rfl⟩,?_⟩
    change (τ : W → W)^[segmentDistance H (inner a) i+e] (mark (inner a)) = w
    rwa [Nat.add_comm,iterate_add_apply,segmentDistance_trace]

/-- Every original arc between ordinary vertices has length one in
the restored tour; a designated shortcut has length two. -/
noncomputable def restoredExceptionalSegments {σ : Equiv.Perm V} {τ : Equiv.Perm (V ⊕ Z)}
    (source : Z ↪ V)
    (hτ : ∀ x y, (restoreExceptionalFactor σ source id).Adj x y ↔ τ x = y) :
    MarkedCycleSegments τ (Embedding.inl : V ↪ V ⊕ Z) σ where
  span v := if v ∈ Set.range source then 2 else 1
  positive v := by split <;> decide
  finish v := by
    by_cases hv : v ∈ Set.range source
    · obtain ⟨z,rfl⟩ := hv
      rw [if_pos (Set.mem_range_self _),iterate_succ_apply' _ 1,iterate_one]
      change τ (τ (.inl (source z))) = .inl (σ (source z))
      rw [(hτ (.inl (source z)) (.inr z)).mp ⟨z,rfl,rfl⟩]
      exact (hτ (.inr z) (.inl (σ (source z)))).mp ⟨z,rfl,rfl⟩
    · rw [if_neg hv,iterate_one]
      exact (hτ (.inl v) (.inl (σ v))).mp ⟨rfl,hv⟩
  interior v i hi hir w := by
    by_cases hv : v ∈ Set.range source
    · rw [if_pos hv] at hir
      have he : i = 1 := by omega
      obtain ⟨z,rfl⟩ := hv
      rw [he,iterate_one]
      change τ (.inl (source z)) ≠ .inl w
      rw [(hτ (.inl (source z)) (.inr z)).mp ⟨z,rfl,rfl⟩]
      exact Sum.inr_ne_inl
    · rw [if_neg hv] at hir
      omega
  covers w := by
    cases w with
    | inl v => exact ⟨v,0,by split <;> decide,rfl⟩
    | inr z =>
      refine ⟨source z,1,by rw [if_pos (Set.mem_range_self _)]; decide,?_⟩
      rw [iterate_one]
      exact (hτ (.inl (source z)) (.inr z)).mp ⟨z,rfl,rfl⟩

end OverfullWork.DirectedRobustExpansion
