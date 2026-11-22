module

public import OverfullWork.MultigraphPartition

@[expose] public section


/-!
# Orienting the distinguished centre of a balanced partition

If the centre has larger internal degree, exchange it with its prescribed
partner and rename the sides. Degree discrepancies increase by at most
twice the maximum multiplicity. This is not a colouring step.
-/

namespace SimpleGraph.MultiGraph

open Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def exchangePart (L : Finset V) (x y : V) : Finset V := insert y (L.erase x)

omit [Fintype V] in
theorem exchangePart_card (L : Finset V) (x y : V) (hx : x ∈ L) (hy : y ∉ L) :
    (exchangePart L x y).card = L.card := by
  have hye : y ∉ L.erase x := fun h => hy (mem_of_mem_erase h)
  rw [exchangePart, card_insert_of_notMem hye, card_erase_of_mem hx]
  have hp : 0 < L.card := card_pos.mpr ⟨x,hx⟩
  omega

omit [Fintype V] in
theorem exchangePart_degree (M : MultiGraph V) (L : Finset V) (x y : V)
    (hx : x ∈ L) (hy : y ∉ L) (v : V) :
    M.degreeInto (exchangePart L x y) v + M.mult s(v,x) =
      M.degreeInto L v + M.mult s(v,y) := by
  have hye : y ∉ L.erase x := fun h => hy (mem_of_mem_erase h)
  have he := sum_erase_add L (fun u => M.mult s(v,u)) hx
  rw [degreeInto, exchangePart, sum_insert hye]
  dsimp only [degreeInto]
  omega

theorem exchangePart_compl_degree (M : MultiGraph V) (L : Finset V) (x y : V)
    (hx : x ∈ L) (hy : y ∉ L) (v : V) :
    M.degreeInto (exchangePart L x y)ᶜ v + M.mult s(v,y) =
      M.degreeInto Lᶜ v + M.mult s(v,x) := by
  have h := M.exchangePart_degree L x y hx hy v
  have h₁ := M.degreeInto_add_compl L v
  have h₂ := M.degreeInto_add_compl (exchangePart L x y) v
  omega

theorem exchangePart_discrepancy (M : MultiGraph V) (L : Finset V) (x y : V)
    (hx : x ∈ L) (hy : y ∉ L) (K B : ℝ)
    (hmu : ∀ u v, (M.mult s(u,v):ℝ) ≤ K)
    (hdis : ∀ v, |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| < B) :
    ∀ v, |(M.degreeInto (exchangePart L x y)ᶜ v:ℝ) -
      (M.degreeInto (exchangePart L x y) v:ℝ)| < B + 2*K := by
  intro v
  have h₁ : (M.degreeInto (exchangePart L x y) v:ℝ) + (M.mult s(v,x):ℝ) =
      (M.degreeInto L v:ℝ) + (M.mult s(v,y):ℝ) := by
    exact_mod_cast M.exchangePart_degree L x y hx hy v
  have h₂ : (M.degreeInto (exchangePart L x y)ᶜ v:ℝ) + (M.mult s(v,y):ℝ) =
      (M.degreeInto Lᶜ v:ℝ) + (M.mult s(v,x):ℝ) := by
    exact_mod_cast M.exchangePart_compl_degree L x y hx hy v
  have hx₀ : (0:ℝ) ≤ (M.mult s(v,x):ℝ) := Nat.cast_nonneg _
  have hy₀ : (0:ℝ) ≤ (M.mult s(v,y):ℝ) := Nat.cast_nonneg _
  have hx₁ := hmu v x
  have hy₁ := hmu v y
  obtain ⟨hl,hr⟩ := abs_lt.mp (hdis v)
  rw [abs_lt]
  constructor <;> linarith

/-- The centre remains separated from its partner and its crossing degree
is at least its internal degree. The error increase is explicit. -/
theorem exists_center_oriented_partition (M : MultiGraph V) (L : Finset V) (x y : V)
    (hx : x ∈ L) (hy : y ∉ L) (hbal : L.card = Lᶜ.card) (K B : ℝ) (hK : 0 ≤ K)
    (hmu : ∀ u v, (M.mult s(u,v):ℝ) ≤ K)
    (hdis : ∀ v, |(M.degreeInto L v:ℝ) - (M.degreeInto Lᶜ v:ℝ)| < B) :
    ∃ A : Finset V, A.card = L.card ∧ Aᶜ.card = Lᶜ.card ∧ x ∈ A ∧ y ∉ A ∧
      M.degreeInto A x ≤ M.degreeInto Aᶜ x ∧
      ∀ v, |(M.degreeInto A v:ℝ) - (M.degreeInto Aᶜ v:ℝ)| < B+2*K := by
  by_cases hcross : M.degreeInto L x ≤ M.degreeInto Lᶜ x
  · refine ⟨L,rfl,rfl,hx,hy,hcross,fun v => ?_⟩
    exact (hdis v).trans_le (by linarith)
  · let S := exchangePart L x y
    have hxy : x ≠ y := fun h => hy (h ▸ hx)
    have hxS : x ∉ S := by simp [S,exchangePart,hxy]
    have hyS : y ∈ S := by simp [S,exchangePart]
    have hcard : S.card = L.card := exchangePart_card L x y hx hy
    have hcomp : Sᶜ.card = Lᶜ.card := by simp only [card_compl,hcard]
    have hxx : M.mult s(x,x) = 0 := M.loopless _ (by simp)
    have hc := M.exchangePart_degree L x y hx hy x
    have hi := M.exchangePart_compl_degree L x y hx hy x
    rw [hxx] at hc hi
    refine ⟨Sᶜ,hcomp.trans hbal.symm,by simpa using hcard.trans hbal,by simpa,by simpa,?_,?_⟩
    · simpa only [compl_compl] using (show M.degreeInto Sᶜ x ≤ M.degreeInto S x by
        dsimp [S]
        omega)
    · intro v
      simpa only [compl_compl] using M.exchangePart_discrepancy L x y hx hy K B hmu hdis v

end SimpleGraph.MultiGraph

namespace OverfullWork.MultigraphExtension

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ready-to-use partition for the current dense extension family, including
the centre orientation used before colouring the internal edges. The
discrepancy after orientation is less than m/7. -/
theorem exists_dense_oriented_point_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (y : V) (m : ℕ) (hm : 24576 ≤ m) (hcard : Fintype.card V+1 = 2*m)
    (hgap : G.maxDegree-G.minDegree ≤ 2)
    (hsat : 2*G.edgeFinset.card = G.maxDegree*(Fintype.card V-1))
    (hdense : 6*(Fintype.card V+1) ≤ 7*G.maxDegree) :
    ∃ L : Finset (Option V), L.card = m ∧ Lᶜ.card = m ∧
      none ∈ L ∧ some y ∉ L ∧
      (pointExtension G).degreeInto L none ≤ (pointExtension G).degreeInto Lᶜ none ∧
      (∀ v, |((pointExtension G).degreeInto L v:ℝ) -
        ((pointExtension G).degreeInto Lᶜ v:ℝ)| < (m:ℝ)/7) ∧
      ∀ v, 3*m < 4*(pointExtension G).degreeInto L v ∧
        3*m < 4*(pointExtension G).degreeInto Lᶜ v := by
  obtain ⟨L,hL,hC,hx,hy,hdis,_⟩ :=
    exists_dense_balanced_point_partition G y m hm hcard hgap hsat hdense
  have hmu : ∀ u v, ((pointExtension G).mult s(u,v):ℝ) ≤ 2 := by
    intro u v
    exact_mod_cast multiplicity_le_two G hgap s(u,v)
  obtain ⟨A,hA,hAc,hxA,hyA,hcross,hdisA⟩ :=
    (pointExtension G).exists_center_oriented_partition L none (some y) hx hy
      (hL.trans hC.symm) 2 ((m:ℝ)/8) (by norm_num) hmu hdis
  have hm' : (24576:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hcap : (m:ℝ)/8+2*2 ≤ (m:ℝ)/7 := by linarith
  have hdis7 : ∀ v, |((pointExtension G).degreeInto A v:ℝ) -
      ((pointExtension G).degreeInto Aᶜ v:ℝ)| < (m:ℝ)/7 :=
    fun v => (hdisA v).trans_le hcap
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
  have hreg := regular_of_saturated G hn hsat
  have hd : 12*m ≤ 7*G.maxDegree := by omega
  have hd' : 12*(m:ℝ) ≤ 7*(G.maxDegree:ℝ) := by exact_mod_cast hd
  refine ⟨A,hA.trans hL,hAc.trans hC,hxA,hyA,hcross,hdis7,fun v => ?_⟩
  have hs : ((pointExtension G).degreeInto A v:ℝ) +
      ((pointExtension G).degreeInto Aᶜ v:ℝ) = (G.maxDegree:ℝ) := by
    exact_mod_cast ((pointExtension G).degreeInto_add_compl A v).trans (hreg v)
  obtain ⟨hl,hr⟩ := abs_lt.mp (hdis7 v)
  constructor
  · have h : 3*(m:ℝ) < 4*((pointExtension G).degreeInto A v:ℝ) := by linarith
    exact_mod_cast h
  · have h : 3*(m:ℝ) < 4*((pointExtension G).degreeInto Aᶜ v:ℝ) := by linarith
    exact_mod_cast h

end OverfullWork.MultigraphExtension
