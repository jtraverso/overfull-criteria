module

public import OverfullWork.PairedRouteEndpoints

@[expose] public section


/-! # The two CMS backwards path constructions with explicit reserves

All choices are deduced from finite predecessor counts. The output is
a route through disjoint matching pairs and a genuinely simple path,
not a supplied walk or an assumed path-existence statement.
-/
namespace OverfullWork.PairedRoutes
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

theorem safe_ne_fixed (τ : Equiv.Perm V) (U : Finset V) (hNe : ∀ x ∈ U, τ x ≠ x)
    (a : V) (ha : τ a=a) (x : V) (hx : x ∈ U) : x ≠ a := by
  intro he;subst x;exact hNe a hx ha

theorem exists_direct_path (τ : Equiv.Perm V) (hτ : ∀ v, τ (τ v)=v)
    (F K : SimpleGraph V) [DecidableRel F.Adj] (U : Finset V)
    (hNe : ∀ v ∈ U, τ v ≠ v) (hK : ∀ v ∈ U, K.Adj v (τ v))
    (S : ℕ → Finset V) (n : ℕ) (hLayers : ∀ j, j ≤ n → S j ⊆ U)
    (hSteps : ∀ j, j < n → ∀ z ∈ S (j+1),
      2+2*n < ((S j).filter (fun x => F.Adj (τ x) z)).card)
    (a b : V) (hab : a ≠ b) (ha : τ a=a) (hb : τ b=b)
    (hStart : ∀ x ∈ S 0, F.Adj a x) (z : V) (hz : z ∈ S n) (hEnd : F.Adj (τ z) b) :
    ∃ r : Route τ F U z n, r.first ∈ S 0 ∧ r.vertices.Nodup ∧
      (∀ v ∈ r.vertices, v ∉ ({a,b}:Finset V)) ∧
      ∃ hA : F.Adj a r.first, (r.close K hK a b hA hEnd).IsPath ∧
        (r.close K hK a b hA hEnd).length=2*n+3 := by
  let B : Finset V := {a,b}
  have hB : B.card ≤ 2 := (card_insert_le _ _).trans (by simp)
  have hClosed : ∀ v ∈ B, τ v ∈ B := by
    intro v hv
    simp only [B,mem_insert,mem_singleton] at hv ⊢
    rcases hv with hv|hv <;> subst v <;> simp [ha,hb]
  have hzU := hLayers n le_rfl hz
  have hzB : z ∉ B := by
    simp only [B,mem_insert,mem_singleton,not_or]
    exact ⟨safe_ne_fixed τ U hNe a ha z hzU,safe_ne_fixed τ U hNe b hb z hzU⟩
  obtain ⟨r,hr,hAvoid,hFirst⟩ := exists_layered_route τ hτ F U hNe S n hLayers B hClosed
    (fun j hj y hy => by have hh := hSteps j hj y hy;omega) z hz hzB
  have hA := hStart r.first hFirst
  refine ⟨r,hFirst,hr,hAvoid,hA,?_,r.length_close K hK a b hA hEnd⟩
  apply r.close_isPath K hK a b hA hEnd hr
  · intro hv;exact hAvoid a hv (by simp [B])
  · intro hv;exact hAvoid b hv (by simp [B])
  · exact hab

theorem exists_extra_path (τ : Equiv.Perm V) (hτ : ∀ v, τ (τ v)=v)
    (F K : SimpleGraph V) [DecidableRel F.Adj] (U : Finset V)
    (hNe : ∀ v ∈ U, τ v ≠ v) (hK : ∀ v ∈ U, K.Adj v (τ v))
    (S : ℕ → Finset V) (n : ℕ) (hLayers : ∀ j, j ≤ n → S j ⊆ U)
    (hSteps : ∀ j, j < n → ∀ z ∈ S (j+1),
      4+2*n < ((S j).filter (fun x => F.Adj (τ x) z)).card)
    (a b : V) (hab : a ≠ b) (ha : τ a=a) (hb : τ b=b)
    (hStart : ∀ x ∈ S 0, F.Adj a x) (z : V) (hz : z ∈ S n)
    (T : Finset V) (hT : T ⊆ U) (hLast : ∀ y ∈ T, F.Adj y b)
    (hTail : 2 < (T.filter (fun y => F.Adj (τ y) (τ z))).card) :
    ∃ y : V, ∃ hyT : y ∈ T, ∃ r : Route τ F U z n, r.first ∈ S 0 ∧ r.vertices.Nodup ∧
      (∀ v ∈ r.vertices, v ∉ ({a,b,y,τ y}:Finset V)) ∧
      ∃ hA : F.Adj a r.first, ∃ hEnd : F.Adj (τ z) (τ y),
        (r.closeExtra K hK a b y (hT hyT) hA hEnd (hLast y hyT)).IsPath ∧
        (r.closeExtra K hK a b y (hT hyT) hA hEnd (hLast y hyT)).length=2*n+5 := by
  let N := T.filter (fun y => F.Adj (τ y) (τ z))
  have hPair : ({z,τ z}:Finset V).card ≤ 2 := (card_insert_le _ _).trans (by simp)
  have hNonempty : (N\{z,τ z}).Nonempty := by
    have hh := card_le_card_sdiff_add_card (s := N) (t := {z,τ z})
    apply card_pos.mp
    change 2 < N.card at hTail
    omega
  obtain ⟨y,hy⟩ := hNonempty
  obtain ⟨hyN,hyOut⟩ := mem_sdiff.mp hy
  obtain ⟨hyT,hEdge⟩ := mem_filter.mp hyN
  have hyU := hT hyT
  have hzU := hLayers n le_rfl hz
  have hyz : y ≠ z := fun he => hyOut (by simp [he])
  have hyτz : y ≠ τ z := fun he => hyOut (by simp [he])
  have hzτy : z ≠ τ y := by
    intro hh
    have hh' := congrArg τ hh
    rw [hτ] at hh'
    exact hyτz hh'.symm
  let B : Finset V := {a,b,y,τ y}
  have hB : B.card ≤ 4 := by
    have h₁ := card_insert_le a ({b,y,τ y}:Finset V)
    have h₂ := card_insert_le b ({y,τ y}:Finset V)
    have h₃ := card_insert_le y ({τ y}:Finset V)
    simp only [card_singleton] at h₃
    change B.card ≤ _ at h₁
    omega
  have hClosed : ∀ v ∈ B, τ v ∈ B := by
    intro v hv
    simp only [B,mem_insert,mem_singleton] at hv ⊢
    rcases hv with hv|hv|hv|hv <;> subst v <;> simp [ha,hb,hτ]
  have hzB : z ∉ B := by
    simp only [B,mem_insert,mem_singleton,not_or]
    exact ⟨safe_ne_fixed τ U hNe a ha z hzU,safe_ne_fixed τ U hNe b hb z hzU,hyz.symm,hzτy⟩
  obtain ⟨r,hr,hAvoid,hFirst⟩ := exists_layered_route τ hτ F U hNe S n hLayers B hClosed
    (fun j hj v hv => by have hh := hSteps j hj v hv;omega) z hz hzB
  have hA := hStart r.first hFirst
  have hEnd := hEdge.symm
  refine ⟨y,hyT,r,hFirst,hr,hAvoid,hA,hEnd,?_,r.length_closeExtra K hK a b y hyU hA hEnd (hLast y hyT)⟩
  apply r.closeExtra_isPath K hK a b y hyU hA hEnd (hLast y hyT) hr hAvoid hab
  · exact (safe_ne_fixed τ U hNe a ha y hyU).symm
  · intro hh
    have hh' := congrArg τ hh
    rw [ha,hτ] at hh'
    exact safe_ne_fixed τ U hNe a ha y hyU hh'.symm
  · exact (safe_ne_fixed τ U hNe b hb y hyU).symm
  · intro hh
    have hh' := congrArg τ hh
    rw [hb,hτ] at hh'
    exact safe_ne_fixed τ U hNe b hb y hyU hh'.symm
  · exact (hNe y hyU).symm

end OverfullWork.PairedRoutes
