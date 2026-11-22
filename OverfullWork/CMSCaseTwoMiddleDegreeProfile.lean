module

public import OverfullWork.CMSCaseTwoMiddleCopies

@[expose] public section


/-! CMS Claim 5.1 for the constructed internal-plus-middle graph, with
explicit finite accounting for the degree and allocation errors. -/
namespace OverfullWork.CMSBalancedCut

open Finset SimpleGraph RegularHeavyCutRepair
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {M : MultiGraph V} {a b w : V} {d m L r t B : ℕ} {η : ℝ}
variable {s : CaseTwoPartition M a b d m L r t η}

theorem CaseTwoPartition.partner_weight_light (s : CaseTwoPartition M a b d m L r t η)
    (v : V) : s.partnerWeight v ≤ L := by
  dsimp only [CaseTwoPartition.partnerWeight]
  split_ifs with hv
  · exact s.partners_light _ (s.partnerEquiv ⟨v,hv⟩).property
  · exact Nat.zero_le _

theorem CaseTwoPartition.centred_discrepancy (s : CaseTwoPartition M a b d m L r t η)
    (hReg : M.IsRegularOfDegree d)
    (hOff : ∀ v, v ≠ a → (∑ w ∈ univ.erase a, (M.mult s(v,w)-1)) ≤ B)
    (v : V) (hv : v ≠ a) :
    |2*(M.degreeInto s.part v:ℝ)-(d:ℝ)-
      ((M.mult s(a,v)-1:ℕ):ℝ)| ≤ η*(m:ℕ)+(B:ℝ) := by
  have hh := M.centred_degree_discrepancy s.part a v s.centre_mem
  have hreg : M.degree v = d := hReg v
  have hswap : M.mult s(v,a) = M.mult s(a,v) :=
    congrArg M.mult Sym2.eq_swap
  rw [hreg,hswap] at hh
  have he : ((∑ u ∈ univ.erase a, (M.mult s(v,u)-1):ℕ):ℝ) ≤ B := by
    exact_mod_cast hOff v hv
  exact hh.trans (add_le_add (s.simple_discrepancy v).le he)

theorem CaseTwoMiddleCopies.degree_profile (r : CaseTwoMiddleCopies s w)
    (hReg : M.IsRegularOfDegree d)
    (hOff : ∀ v, v ≠ a → (∑ w ∈ univ.erase a, (M.mult s(v,w)-1)) ≤ B)
    (v : V) :
    |2*(r.graph.degree v:ℝ)-(d:ℝ)| ≤
      η*(m:ℕ)+(B:ℝ)+(L:ℕ)+
      2*((M.mult s(b,w)-M.degreeInto s.part a:ℕ):ℝ)+
      2*(s.heavyVertices.card:ℝ)+3 := by
  let F := M.mult s(b,w)-M.degreeInto s.part a
  have hη : 0 ≤ η*(m:ℕ) :=
    (abs_nonneg _).trans (s.simple_discrepancy a).le
  have hB : (0:ℝ) ≤ B := Nat.cast_nonneg _
  have hL : (0:ℝ) ≤ L := Nat.cast_nonneg _
  have hF : (0:ℝ) ≤ F := Nat.cast_nonneg _
  have hH : (0:ℝ) ≤ s.heavyVertices.card := Nat.cast_nonneg _
  change |2*(r.graph.degree v:ℝ)-(d:ℝ)| ≤
    η*(m:ℕ)+(B:ℝ)+(L:ℝ)+2*(F:ℝ)+2*(s.heavyVertices.card:ℝ)+3
  by_cases hv : v = a
  · subst v
    have hh := r.centre_bounds hReg
    have hl : d ≤ 2*r.graph.degree a+1 := by omega
    have hlR : (d:ℝ) ≤ 2*(r.graph.degree a:ℝ)+1 := by exact_mod_cast hl
    have huR : 2*(r.graph.degree a:ℝ) ≤ (d:ℝ)+(F:ℝ) := by exact_mod_cast hh.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hdisc := abs_le.mp (s.centred_discrepancy hReg hOff v hv)
  have hdegree := MiddleCopyGraph.other_degree M s.part a v r.count
    (r.inside_zero _ s.centre_mem) hv
  change r.graph.degree v = _ at hdegree
  let q := M.mult s(a,v)
  let e := q-1
  have heq : e ≤ q := Nat.sub_le _ _
  have hqe : q ≤ e+1 := by dsimp only [e];omega
  have heqR : (e:ℝ) ≤ q := by exact_mod_cast heq
  have hqeR : (q:ℝ) ≤ (e:ℝ)+1 := by exact_mod_cast hqe
  change -(η*(m:ℕ)+(B:ℝ)) ≤
      2*(M.degreeInto s.part v:ℝ)-(d:ℝ)-(e:ℝ) ∧
    2*(M.degreeInto s.part v:ℝ)-(d:ℝ)-(e:ℝ) ≤
      η*(m:ℕ)+(B:ℝ) at hdisc
  by_cases hvA : v ∈ s.part
  · have hvb : v ≠ b := fun he => s.second_not_mem (he ▸ hvA)
    have hqL : q ≤ L := by
      by_contra! hq
      exact s.heavy_across v hvb hq hvA
    have hqLR : (q:ℝ) ≤ L := by exact_mod_cast hqL
    rw [if_pos hvA,r.inside_zero v hvA,add_zero] at hdegree
    have hdegR : (r.graph.degree v:ℝ) = M.degreeInto s.part v := by exact_mod_cast hdegree
    rw [hdegR]
    have he0 : (0:ℝ) ≤ e := Nat.cast_nonneg _
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  rw [if_neg hvA] at hdegree
  have hdegR : (r.graph.degree v:ℝ) = (M.degreeInto s.partᶜ v:ℝ)+(r.count v:ℝ) := by
    exact_mod_cast hdegree
  have hsplit := M.degreeInto_add_compl s.part v
  have hreg : M.degree v = d := hReg v
  rw [hreg] at hsplit
  have hsplitR : (M.degreeInto s.part v:ℝ)+(M.degreeInto s.partᶜ v:ℝ) =
      d := by exact_mod_cast hsplit
  have hcross : s.crossWeight v = q := if_pos (mem_compl.mpr hvA)
  have hu := r.bundle_upper v
  rw [hcross] at hu
  have huR : 2*(r.count v:ℝ) ≤ (q:ℝ)+(F:ℝ)+1 := by exact_mod_cast hu
  have hlR : (q:ℝ) ≤ 2*(r.count v:ℝ)+(L:ℝ)+2*((F:ℝ)+(s.heavyVertices.card:ℝ)+1) := by
    by_cases hvH : v ∈ s.heavyVertices
    · have hl := r.paired_lower v hvH
      rw [hcross] at hl
      have hp : (s.partnerWeight v:ℝ) ≤ L := by exact_mod_cast s.partner_weight_light v
      have hd : r.balancing.deficit v ≤ F+s.heavyVertices.card+1 :=
        (single_le_sum (f := r.balancing.deficit) (fun _ _ => Nat.zero_le _) (mem_univ v)).trans
          r.deficit_budget
      have hdR : (r.balancing.deficit v:ℝ) ≤ (F:ℝ)+(s.heavyVertices.card:ℝ)+1 := by exact_mod_cast hd
      have hlR : (q:ℝ) ≤ 2*(r.count v:ℝ)+(s.partnerWeight v:ℝ)+2*(r.balancing.deficit v:ℝ) := by
        exact_mod_cast hl
      linarith
    · have hqL : q ≤ L := by
        by_contra! hq
        have hbv : v ≠ b := by
          intro he
          apply hvH
          change v ∈ insert b _
          exact mem_insert.mpr (Or.inl he)
        exact hvH (mem_insert_of_mem ((heavySet_mem _ _ _ _ _).mpr ⟨hbv,hq⟩))
      have hqLR : (q:ℝ) ≤ L := by exact_mod_cast hqL
      have hg0 : (0:ℝ) ≤ r.count v := Nat.cast_nonneg _
      linarith
  rw [hdegR]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end OverfullWork.CMSBalancedCut
