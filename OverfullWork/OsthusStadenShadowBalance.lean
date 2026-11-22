module

public import OverfullWork.OsthusStadenShadowExpansion
public import OverfullWork.DirectedMultiplicityDemands

@[expose] public section


/-! Shadow endpoints and balance identities in Osthus–Staden §5.8.
The source and target of a shadow vertex are consecutive on its factor. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {U : Type*} [Fintype U]

noncomputable def shadowSend (σ : Equiv.Perm U) (incoming outgoing : Finset U)
    (v : ↥(incoming ∪ outgoing)) : U :=
  if (v:U) ∈ incoming then σ.symm v else v

noncomputable def shadowReceive (σ : Equiv.Perm U) (incoming outgoing : Finset U)
    (v : ↥(incoming ∪ outgoing)) : U :=
  σ (shadowSend σ incoming outgoing v)

omit [Fintype U] in
theorem shadowSend_injective (σ : Equiv.Perm U) (incoming outgoing : Finset U)
    (hSep : ∀ u ∈ outgoing, σ u ∉ incoming) :
    Function.Injective (shadowSend σ incoming outgoing) := by
  intro x y h
  apply Subtype.ext
  by_cases hx : (x:U) ∈ incoming <;> by_cases hy : (y:U) ∈ incoming
  · exact σ.symm.injective (by simpa [shadowSend,hx,hy] using h)
  · have hyo := (mem_union.mp y.property).resolve_left hy
    have he : σ.symm (x:U) = (y:U) := by simpa [shadowSend,hx,hy] using h
    have he' := congrArg σ he
    rw [σ.apply_symm_apply] at he'
    exact (hSep y hyo (he' ▸ hx)).elim
  · have hxo := (mem_union.mp x.property).resolve_left hx
    have he : (x:U) = σ.symm (y:U) := by simpa [shadowSend,hx,hy] using h
    have he' := congrArg σ he
    rw [σ.apply_symm_apply] at he'
    exact (hSep x hxo (he'.symm ▸ hy)).elim
  · simpa [shadowSend,hx,hy] using h

/-- Add the same baseline to the two demands of each red cluster.
The two total demands agree as soon as the two exceptional totals do. -/
theorem shadow_demands_balance {T : Type*} [Fintype T] (sin sout : T → ℕ) (c : ℕ)
    (h : (∑ v : T,sin v) = (∑ v : T,sout v)) :
    (∑ v : T, (c + sin v)) = (∑ v : T, (c + sout v)) := by
  simp only [sum_add_distrib,h]

omit [Fintype U] in
/-- Equation (41) after the addition of shadow arcs. In the support of
the shadow source map, its corresponding target is the successor.
Outside that support both exceptional totals involved are zero. -/
theorem balance_after_shadow_demands (σ : Equiv.Perm U) (incoming outgoing : Finset U)
    (sin sout bout bin : U → ℕ) (c : ℕ)
    (hDis : Disjoint incoming outgoing) (hSep : ∀ u ∈ outgoing, σ u ∉ incoming)
    (hIn : ∀ u, u ∉ incoming → sin u = 0) (hOut : ∀ u, u ∉ outgoing → sout u = 0)
    (hBout : ∀ v : ↥(incoming ∪ outgoing), bout (shadowSend σ incoming outgoing v) = c + sin v)
    (hBin : ∀ v : ↥(incoming ∪ outgoing), bin (shadowReceive σ incoming outgoing v) = c + sout v)
    (hZeroOut : ∀ u, u ∉ Set.range (shadowSend σ incoming outgoing) → bout u = 0)
    (hZeroIn : ∀ u, u ∉ Set.range (shadowReceive σ incoming outgoing) → bin u = 0) :
    ∀ u, sout u + bout u = sin (σ u) + bin (σ u) := by
  intro u
  by_cases hu : u ∈ Set.range (shadowSend σ incoming outgoing)
  · obtain ⟨v,rfl⟩ := hu
    rw [hBout,show σ (shadowSend σ incoming outgoing v) = shadowReceive σ incoming outgoing v from rfl,
      hBin]
    by_cases hv : (v:U) ∈ incoming
    · have hv' : (v:U) ∉ outgoing := fun h => disjoint_left.mp hDis hv h
      have hp : σ.symm (v:U) ∉ outgoing := by
        intro h
        apply hSep (σ.symm (v:U)) h
        simpa only [σ.apply_symm_apply] using hv
      simp only [shadowSend,shadowReceive,hv,if_true,σ.apply_symm_apply,hOut _ hp,hOut _ hv']
      omega
    · have hv' : (v:U) ∈ outgoing := (mem_union.mp v.property).resolve_left hv
      have hn := hSep v hv'
      simp only [shadowSend,shadowReceive,hv,if_false,hIn _ hv,hIn _ hn]
      omega
  · have hs : u ∉ outgoing := by
      intro hs
      by_cases h : u ∈ incoming
      · exact disjoint_left.mp hDis h hs
      · let v : ↥(incoming ∪ outgoing) := ⟨u,mem_union_right _ hs⟩
        exact hu ⟨v,by simp [shadowSend,v,h]⟩
    have ht : σ u ∉ incoming := by
      intro h
      let v : ↥(incoming ∪ outgoing) := ⟨σ u,mem_union_left _ h⟩
      exact hu ⟨v,by simp [shadowSend,v,h]⟩
    have hRecv : σ u ∉ Set.range (shadowReceive σ incoming outgoing) :=
      fun ⟨v,h⟩ => hu ⟨v,σ.injective h⟩
    rw [hOut u hs,hZeroOut u hu,hIn _ ht,hZeroIn _ hRecv]

/-- Capacity-limited shadow arcs realizing the demands. The numerical
hierarchy and rounding margins are those of the already proved Lema 4.1. -/
theorem exists_shadow_balancing_matrix {T : Type*} [Fintype T]
    (R : Digraph T) (b c : ℕ) (ν τ α ε : ℝ) (sin sout : T → ℕ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hντ : ν ≤ τ) (hτα : 4*τ ≤ α)
    (hε : 0 ≤ ε) (hεν : 16*ε ≤ ν) (hOrder : 8 ≤ α*(Fintype.card T:ℝ))
    (hCap : 3*((c:ℝ)/(Fintype.card T:ℝ)) ≤ (b:ℝ)*ν^2)
    (hR : IsRealRobust R ν τ)
    (hIn : ∀ v, α*(Fintype.card T:ℝ) ≤ (inDegree R v:ℝ))
    (hOut : ∀ v, α*(Fintype.card T:ℝ) ≤ (outDegree R v:ℝ))
    (hSin : ∀ v, (sin v:ℝ) ≤ ε*(c:ℝ)) (hSout : ∀ v, (sout v:ℝ) ≤ ε*(c:ℝ))
    (hBalance : (∑ v,sin v) = ∑ v,sout v) :
    ∃ M : T → T → ℕ,
      (∀ v w, M v w ≤ if R.Adj v w then b else 0) ∧
      (∀ v, (∑ w,M v w) = c+sin v) ∧ (∀ w, (∑ v,M v w) = c+sout w) := by
  have hCard : 0 < (Fintype.card T:ℝ) := by
    have h0 : 0 ≤ (Fintype.card T:ℝ) := Nat.cast_nonneg _
    by_contra! h
    have he : (Fintype.card T:ℝ) = 0 := le_antisymm h h0
    rw [he,mul_zero] at hOrder
    norm_num at hOrder
  let ρ := (c:ℝ)/(Fintype.card T:ℝ)
  have he : ρ*(Fintype.card T:ℝ) = c := div_mul_cancel₀ _ hCard.ne'
  have hBounds (f : T → ℕ) (hf : ∀ v, (f v:ℝ) ≤ ε*(c:ℝ)) (v : T) :
      (1-ε)*ρ*(Fintype.card T:ℝ) ≤ ((c+f v:ℕ):ℝ) ∧
      ((c+f v:ℕ):ℝ) ≤ (1+ε)*ρ*(Fintype.card T:ℝ) := by
    simp only [mul_assoc,he,Nat.cast_add]
    constructor
    · nlinarith only [mul_nonneg hε (Nat.cast_nonneg c : (0:ℝ) ≤ _),Nat.cast_nonneg (f v) (α := ℝ)]
    · nlinarith only [hf v]
  apply DirectedMultigraphFactors.osthus_staden_lemma_4_1
    (fun v w => if R.Adj v w then b else 0) R b ν τ α ε ρ
    (fun v => c+sin v) (fun v => c+sout v) hν hν1 hντ hτα hε hεν
    (div_nonneg (Nat.cast_nonneg _) hCard.le) hCap hOrder
    (fun v w h => by simp [h]) hR hIn hOut (hBounds sin hSin) (hBounds sout hSout)
    (shadow_demands_balance sin sout c hBalance)

end OverfullWork.DirectedRobustExpansion
