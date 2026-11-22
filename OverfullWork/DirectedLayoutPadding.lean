module

public import OverfullWork.DirectedBatchResidual

@[expose] public section


/-! Put layouts with different index types on a common finite index.
Padding uses fixed occurrences only, so it neither spends host arcs nor
adds boundary vertices. Erasing the padding preserves every route. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset
open scoped Classical
variable {V I K : Type*} [Fintype K]

noncomputable def layoutIndex (f : I ↪ K) (fallback : I) (j : K) : I :=
  if h : ∃ i, f i = j then h.choose else fallback

private theorem layoutIndex_in_range (f : I ↪ K) (fallback : I) (j : K) (hj : j ∈ Set.range f) :
    f (layoutIndex f fallback j) = j := by
  have h : ∃ i, f i = j := hj
  rw [layoutIndex,dif_pos h]
  exact h.choose_spec

private theorem layoutIndex_apply (f : I ↪ K) (fallback : I) (i : I) :
    layoutIndex f fallback (f i) = i :=
  f.injective (layoutIndex_in_range f fallback (f i) (Set.mem_range_self i))

/-- Pad outside the image by fixed copies with the endpoints of the
distinguished occurrence, which are already in the boundary. -/
noncomputable def Layout.pad (L : Layout V I) (long : I) (f : I ↪ K) : Layout V K where
  boundary := L.boundary
  source := fun j => L.source (layoutIndex f long j)
  target := fun j => L.target (layoutIndex f long j)
  fixed := univ.filter fun j => j ∉ Set.range f ∨ layoutIndex f long j ∈ L.fixed
  ends := fun j => L.ends (layoutIndex f long j)

@[simp] theorem Layout.pad_source (L : Layout V I) (long : I) (f : I ↪ K) (i : I) :
    (L.pad long f).source (f i) = L.source i := by simp [Layout.pad,layoutIndex_apply]

@[simp] theorem Layout.pad_target (L : Layout V I) (long : I) (f : I ↪ K) (i : I) :
    (L.pad long f).target (f i) = L.target i := by simp [Layout.pad,layoutIndex_apply]

@[simp] theorem Layout.mem_pad_fixed (L : Layout V I) (long : I) (f : I ↪ K) (i : I) :
    f i ∈ (L.pad long f).fixed ↔ i ∈ L.fixed := by
  simp [Layout.pad,layoutIndex_apply]

theorem Layout.range_of_flexible (L : Layout V I) (long : I) (f : I ↪ K)
    {j : K} (hj : j ∉ (L.pad long f).fixed) : j ∈ Set.range f := by
  by_contra hn
  exact hj (mem_filter.mpr ⟨mem_univ _,Or.inl hn⟩)

/-- Flexible occurrences of the padded layout are exactly those of the
original layout. -/
noncomputable def Layout.padFlexibleEquiv (L : Layout V I) (long : I) (f : I ↪ K) :
    {i // i ∉ L.fixed} ≃ {j // j ∉ (L.pad long f).fixed} :=
  Equiv.ofBijective (fun i => ⟨f i.val,fun h => i.prop ((L.mem_pad_fixed long f _).1 h)⟩)
    ⟨fun _ _ he => Subtype.ext (f.injective (congrArg Subtype.val he)),fun j => by
      obtain ⟨i,hi⟩ := L.range_of_flexible long f j.prop
      refine ⟨⟨i,fun hf => j.prop (hi ▸ (L.mem_pad_fixed long f i).2 hf)⟩,Subtype.ext hi⟩⟩

theorem Layout.pad_endpointLoad [Fintype I] (L : Layout V I) (long : I) (f : I ↪ K)
    (d : Bool) (v : V) : (L.pad long f).endpointLoad d v = L.endpointLoad d v := by
  unfold Layout.endpointLoad
  rw [← (L.padFlexibleEquiv long f).sum_comp]
  apply sum_congr rfl
  intro i _
  change (if v = (if d then (L.pad long f).target (f i.val)
    else (L.pad long f).source (f i.val)) then (1:ℕ) else 0) = _
  rw [L.pad_target,L.pad_source]

theorem Layout.pad_short_count_le [Fintype I] (L : Layout V I) (long : I) (f : I ↪ K) :
    (univ \ insert (f long) (L.pad long f).fixed).card ≤ Fintype.card I := by
  apply card_le_card_of_injOn (layoutIndex f long) (t := (univ : Finset I))
  · simp
  · intro x hx y hy he
    have x' : x ∉ (L.pad long f).fixed :=
      fun h => (mem_sdiff.mp hx).2 (mem_insert_of_mem h)
    have y' : y ∉ (L.pad long f).fixed :=
      fun h => (mem_sdiff.mp hy).2 (mem_insert_of_mem h)
    have hX := layoutIndex_in_range f long x (L.range_of_flexible long f x')
    have hY := layoutIndex_in_range f long y (L.range_of_flexible long f y')
    exact hX.symm.trans ((congrArg f he).trans hY)

/-- Erase the fixed padding. Every vertex outside the original boundary
is still covered, since it never occurred in a fixed path. -/
def Realization.unpad {D : Digraph V} {L : Layout V I} {long : I} {f : I ↪ K}
    (R : Realization D (L.pad long f)) : Realization D L where
  interior i := R.interior (f i)
  simple i := by simpa only [L.pad_source,L.pad_target] using R.simple (f i)
  fixed_empty i hi := R.fixed_empty (f i) ((L.mem_pad_fixed long f i).2 hi)
  flexible_nonempty i hi := R.flexible_nonempty (f i) (fun h => hi ((L.mem_pad_fixed long f i).1 h))
  flexible_chain i hi := by
    simpa only [L.pad_source,L.pad_target] using
      R.flexible_chain (f i) (fun h => hi ((L.mem_pad_fixed long f i).1 h))
  outside i x h := R.outside (f i) x h
  unique i j h := R.unique (f i) (f j) (fun he => h (f.injective he))
  spans := by
    intro x hx
    obtain ⟨j,hj⟩ := R.spans x hx
    have hflex : j ∉ (L.pad long f).fixed := by
      intro hf
      rw [R.fixed_empty j hf] at hj
      exact List.not_mem_nil hj
    obtain ⟨i,hi⟩ := L.range_of_flexible long f hflex
    exact ⟨i,hi.symm ▸ hj⟩

theorem Realization.used_unpad {D : Digraph V} {L : Layout V I} {long : I} {f : I ↪ K}
    (R : Realization D (L.pad long f)) : R.unpad.used = R.used := by
  ext x y
  simp only [Realization.used,Digraph.iSup_adj,Realization.word]
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨(L.padFlexibleEquiv long f) i,?_⟩
    change List.IsInfix [x,y] ((L.pad long f).source (f i.val) ::
      R.interior (f i.val) ++ [(L.pad long f).target (f i.val)])
    simpa only [L.pad_source,L.pad_target,Realization.unpad,wordGraph] using hi
  · rintro ⟨⟨j,hj⟩,hh⟩
    obtain ⟨i,rfl⟩ := L.range_of_flexible long f hj
    have hn : i ∉ L.fixed := fun h => hj ((L.mem_pad_fixed long f i).2 h)
    exact ⟨⟨i,hn⟩,by simpa only [L.pad_source,L.pad_target,Realization.unpad,wordGraph] using hh⟩

end OverfullWork.DirectedSpanningConfiguration
