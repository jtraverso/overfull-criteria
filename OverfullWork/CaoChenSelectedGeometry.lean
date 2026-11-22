module

public import OverfullWork.CaoChenForkSelection

@[expose] public section


/-! # Seven genuinely distinct vertices from the selected fork arms

The low leaves lie outside the closed neighbourhood of the spine. An
anchor cannot be the low root, since that would create a low-low edge
forbidden by VAL. Distinctness is derived, not supplied as a new premise.
-/
namespace OverfullWork.CaoChenForkSelection
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC CaoChenForkCounting
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem selected_arms_distinct7 (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {a b u : V}
    (hroot : RootedAdmissible c a b u) (d : ℕ)
    (hda : G.degree a≤d) (hdelta : 2*d≤G.maxDegree)
    {m : ℕ} (z t : Fin m → V) (hz : Function.Injective z) (ht : Function.Injective t)
    (hconfig : ∀i,z i∈goodNeighbours c a b u ∧ t i∈goodSecondNeighbours c a b u ∧
      G.degree (t i)≤d ∧ Good c a b (z i) (t i))
    (i j : Fin m) (hij : i≠j) : Distinct7 a b u (z i) (z j) (t i) (t j) := by
  obtain ⟨hcm,α,hbu,hα⟩ := hroot
  have hba : G.Adj b u := c.col_adj hbu
  have hau : a≠u := by
    intro he
    have hh := hbu
    rw [←he,c.col_symm,hcm.uncol] at hh
    cases hh
  have hzN (l : Fin m) : G.Adj u (z l) :=
    (mem_neighborFinset G u (z l)).mp (mem_filter.mp (hconfig l).1).1
  have hzb (l : Fin m) : b≠z l := (mem_filter.mp (hconfig l).1).2.1.symm
  have hza (l : Fin m) : a≠z l := by
    intro he
    obtain ⟨γ,hzt,_⟩ := (hconfig l).2.2.2
    have hv := Overfull.deg_add hcrit (c.col_adj hzt)
    rw [←he] at hv
    have hlow := (hconfig l).2.2.1
    omega
  have hleaf (l : Fin m) : t l≠a ∧ t l≠u ∧ ¬G.Adj u (t l) := by
    have hh := (mem_sdiff.mp (hconfig l).2.1).2
    simpa only [mem_insert,mem_neighborFinset,not_or] using hh
  have htb (l : Fin m) : b≠t l := by
    intro he
    exact (hleaf l).2.2 (he ▸ hba.symm)
  have hzt (l r : Fin m) : z l≠t r := by
    intro he
    exact (hleaf r).2.2 (he ▸ hzN l)
  exact ⟨hcm.adj.ne,hau,hza i,hza j,(hleaf i).1.symm,(hleaf j).1.symm,
    hba.ne,hzb i,hzb j,htb i,htb j,(hzN i).ne,(hzN j).ne,
    (hleaf i).2.1.symm,(hleaf j).2.1.symm,
    fun he => hij (hz he),hzt i i,hzt i j,hzt j i,hzt j j,fun he => hij (ht he)⟩

end OverfullWork.CaoChenForkSelection
