module

/- Port of the user-supplied multigraph model; import and scope notes adapted.
See multigraph-extension-provenance.json. -/
/-
# Multigrafos y el criterio overfull: la capa del caso general del hueco 1

Modelo procedente del ZIP original, con importación acotada y sin `sorry`.

**Por qué multigrafos.** La extensión de un punto del criterio de orden impar
(Plantholt–Shan, doi:10.1002/jgt.23077) es `Δ`-regular **solo** en el caso
máximamente denso `2|E| = Δ(n−1)`; en cualquier otro grafo de orden impar sin
subgrafo `Δ`-overfull el déficit total `∑ v, (Δ − deg v)` supera `Δ`
(`SimpleGraph.maxDegree_le_deficitSum_of_not_overfull`, en
`DeficitArithmetic.lean`). Los vértices deficitarios sobrantes no se pueden
saturar con aristas nuevas al vértice nuevo (cada uno solo admite una), sino
con **aristas paralelas dentro de `V`** entre vértices deficitarios: hay que
trabajar con multigrafos.

**Contenido verificado aquí** (multiplicidad `Sym2 V → ℕ` nula en la diagonal):

* `MultiGraph`, `edgeCount`, `degree`, `IsRegularOfDegree`, `ofSimpleGraph`;
* `sum_degrees_eq_twice_edgeCount` — `∑ v, deg v = 2·|E|` con multiplicidades;
* `card_mul_of_regular`, `even_of_odd_card_of_regular` — **paridad**: un
  multigrafo `k`-regular de orden impar obliga a `k` par;
* `EdgeColoring M k` — coloración propia por copias (`col e i` = copias de `e`
  con color `i`; en cada vértice y color a lo sumo una);
* `two_mul_sum_col_le`, `edgeCount_le_of_edgeColoring` — **lema de conteo
  multigrafo**: `|E(M)| ≤ k·⌊n/2⌋`;
* `IsOverfullWith`, `not_edgeColorable_of_overfull` — **criterio overfull
  multigrafo**: `k·⌊n/2⌋ < |E(M)|` ⟹ `M` no es `k`-arista-coloreable. Es la
  versión multigrafo de `not_EdgeColorable_of_isOverfullOn` del archivo base.
-/
public import OverfullWork.DegreeBudget

@[expose] public section


namespace SimpleGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Un **multigrafo lazo-libre** sobre `V`: una multiplicidad en cada par no
ordenado de vértices, nula en la diagonal (no hay lazos). -/
structure MultiGraph (V : Type*) where
  /-- Multiplicidad de cada par no ordenado. -/
  mult : Sym2 V → ℕ
  /-- No hay lazos. -/
  loopless : ∀ e : Sym2 V, e.IsDiag → mult e = 0

namespace MultiGraph

variable (M : MultiGraph V)

/-- Número de aristas de `M`, contadas con multiplicidad. -/
def edgeCount : ℕ := ∑ e : Sym2 V, M.mult e

/-- Grado de `v` en `M`: suma de multiplicidades de las aristas que lo tocan. -/
def degree (v : V) : ℕ :=
  ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), M.mult e

/-- `M` es `k`-regular. -/
def IsRegularOfDegree (k : ℕ) : Prop := ∀ v : V, M.degree v = k

/-- El conjunto de vértices de una arista es el filtro de los vértices que la
tocan. -/
theorem toFinset_eq_filter (e : Sym2 V) :
    e.toFinset = univ.filter (fun v : V => v ∈ e) := by
  ext v
  simp

/-- El grado como suma con indicador. -/
theorem degree_eq_sum_ite (v : V) :
    M.degree v = ∑ e : Sym2 V, if v ∈ e then M.mult e else 0 := by
  rw [degree, Finset.sum_filter]

/-- **Identidad del doble conteo**: `∑ v, deg v = 2·|E|` (con multiplicidad). -/
theorem sum_degrees_eq_twice_edgeCount :
    ∑ v : V, M.degree v = 2 * M.edgeCount := by
  have hinner : ∀ e : Sym2 V, (∑ v : V, if v ∈ e then M.mult e else 0) =
      2 * M.mult e := by
    intro e
    have h1 : (∑ v : V, if v ∈ e then M.mult e else 0) =
        ∑ v ∈ univ.filter (fun v : V => v ∈ e), M.mult e :=
      (Finset.sum_filter (s := (Finset.univ : Finset V)) (p := fun v : V => v ∈ e)
        (f := fun _ => M.mult e)).symm
    rw [h1, Finset.sum_const_nat (s := univ.filter (fun v : V => v ∈ e))
      (f := fun _ => M.mult e) (m := M.mult e) (fun _ _ => rfl)]
    have hcard : (univ.filter (fun v : V => v ∈ e)).card = e.toFinset.card := by
      rw [toFinset_eq_filter]
    rw [hcard]
    by_cases h : e.IsDiag
    · rw [Sym2.card_toFinset, if_pos h, M.loopless e h]
    · rw [Sym2.card_toFinset, if_neg h]
  calc ∑ v : V, M.degree v
      = ∑ v : V, ∑ e : Sym2 V, (if v ∈ e then M.mult e else 0) :=
        Finset.sum_congr rfl (fun v _ => M.degree_eq_sum_ite v)
    _ = ∑ e : Sym2 V, ∑ v : V, (if v ∈ e then M.mult e else 0) := Finset.sum_comm
    _ = ∑ e : Sym2 V, 2 * M.mult e := Finset.sum_congr rfl (fun e _ => hinner e)
    _ = 2 * M.edgeCount := by
        rw [edgeCount, Finset.mul_sum]

/-- Si `M` es `k`-regular, `n·k = 2·|E|`. -/
theorem card_mul_of_regular {k : ℕ} (h : M.IsRegularOfDegree k) :
    Fintype.card V * k = 2 * M.edgeCount := by
  have h1 : ∑ v : V, M.degree v = ∑ v : V, k := Finset.sum_congr rfl (fun v _ => h v)
  have h2 : (∑ v : V, k) = Fintype.card V * k := by
    rw [Finset.sum_const_nat (s := (univ : Finset V)) (f := fun _ => k) (m := k)
      (fun _ _ => rfl), Finset.card_univ]
  rw [M.sum_degrees_eq_twice_edgeCount, h2] at h1
  omega

/-- **Obstrucción de paridad**: un multigrafo `k`-regular de orden impar obliga
a `k` par. -/
theorem even_of_odd_card_of_regular {k : ℕ} (h : M.IsRegularOfDegree k)
    (hn : Odd (Fintype.card V)) : Even k := by
  have h1 : Fintype.card V * k = 2 * M.edgeCount := M.card_mul_of_regular h
  have h2 : 2 ∣ Fintype.card V * k := ⟨M.edgeCount, h1⟩
  have h3 : Nat.Coprime 2 (Fintype.card V) := Nat.coprime_two_left.mpr hn
  exact even_iff_two_dvd.mpr (Nat.Coprime.dvd_of_dvd_mul_left h3 h2)

/-- Una **coloración propia de aristas por copias**: cada copia de cada arista
recibe un color y en cada vértice no hay dos copias del mismo color. -/
structure EdgeColoring (k : ℕ) where
  /-- Número de copias de la arista `e` que reciben el color `i`. -/
  col : Sym2 V → Fin k → ℕ
  /-- Las copias de `e` suman su multiplicidad. -/
  sum_col : ∀ e : Sym2 V, ∑ i : Fin k, col e i = M.mult e
  /-- En cada vértice y color, a lo sumo una copia. -/
  proper : ∀ (v : V) (i : Fin k),
    ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), col e i ≤ 1

/-- Una arista diagonal no lleva copias coloreadas. -/
theorem col_eq_zero_of_isDiag {k : ℕ} (C : M.EdgeColoring k) {e : Sym2 V}
    (h : e.IsDiag) (i : Fin k) : C.col e i = 0 := by
  have h0 : ∑ j : Fin k, C.col e j = 0 := by
    rw [C.sum_col e, M.loopless e h]
  exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)

/-- Cada color cubre a lo sumo `⌊n/2⌋` aristas (con multiplicidad): sus copias
forman un matching. -/
theorem two_mul_sum_col_le {k : ℕ} (C : M.EdgeColoring k) (i : Fin k) :
    2 * (∑ e : Sym2 V, C.col e i) ≤ Fintype.card V := by
  have hvb : ∀ v : V, (∑ e : Sym2 V, (if v ∈ e then C.col e i else 0)) ≤ 1 := by
    intro v
    have h1 : (∑ e : Sym2 V, (if v ∈ e then C.col e i else 0)) =
        ∑ e ∈ univ.filter (fun e : Sym2 V => v ∈ e), C.col e i :=
      (Finset.sum_filter (s := (Finset.univ : Finset (Sym2 V)))
        (p := fun e : Sym2 V => v ∈ e) (f := fun e => C.col e i)).symm
    rw [h1]
    exact C.proper v i
  have heb : ∀ e : Sym2 V, (∑ v : V, (if v ∈ e then C.col e i else 0)) =
      2 * C.col e i := by
    intro e
    have h1 : (∑ v : V, (if v ∈ e then C.col e i else 0)) =
        ∑ v ∈ univ.filter (fun v : V => v ∈ e), C.col e i :=
      (Finset.sum_filter (s := (Finset.univ : Finset V)) (p := fun v : V => v ∈ e)
        (f := fun _ => C.col e i)).symm
    rw [h1, Finset.sum_const_nat (s := univ.filter (fun v : V => v ∈ e))
      (f := fun _ => C.col e i) (m := C.col e i) (fun _ _ => rfl)]
    have hcard : (univ.filter (fun v : V => v ∈ e)).card = e.toFinset.card := by
      rw [toFinset_eq_filter]
    rw [hcard]
    by_cases h : e.IsDiag
    · rw [Sym2.card_toFinset, if_pos h, M.col_eq_zero_of_isDiag C h i]
    · rw [Sym2.card_toFinset, if_neg h]
  have hstep : (∑ e : Sym2 V, 2 * C.col e i) ≤ Fintype.card V := by
    calc ∑ e : Sym2 V, 2 * C.col e i
        = ∑ e : Sym2 V, ∑ v : V, (if v ∈ e then C.col e i else 0) :=
          Finset.sum_congr rfl (fun e _ => (heb e).symm)
      _ = ∑ v : V, ∑ e : Sym2 V, (if v ∈ e then C.col e i else 0) := Finset.sum_comm
      _ ≤ ∑ v : V, 1 := Finset.sum_le_sum (fun v _ => hvb v)
      _ = Fintype.card V := by simp
  calc 2 * (∑ e : Sym2 V, C.col e i) = ∑ e : Sym2 V, 2 * C.col e i :=
        Finset.mul_sum (s := (Finset.univ : Finset (Sym2 V)))
          (f := fun e => C.col e i) (a := 2)
    _ ≤ Fintype.card V := hstep

/-- **Lema de conteo multigrafo**: `|E(M)| ≤ k·⌊n/2⌋`. -/
theorem edgeCount_le_of_edgeColoring {k : ℕ} (C : M.EdgeColoring k) :
    M.edgeCount ≤ k * (Fintype.card V / 2) := by
  have h1 : M.edgeCount = ∑ i : Fin k, ∑ e : Sym2 V, C.col e i := by
    calc M.edgeCount = ∑ e : Sym2 V, M.mult e := rfl
      _ = ∑ e : Sym2 V, ∑ i : Fin k, C.col e i :=
          Finset.sum_congr rfl (fun e _ => (C.sum_col e).symm)
      _ = ∑ i : Fin k, ∑ e : Sym2 V, C.col e i := Finset.sum_comm
  have h2 : ∀ i : Fin k, (∑ e : Sym2 V, C.col e i) ≤ Fintype.card V / 2 := by
    intro i
    have h := M.two_mul_sum_col_le C i
    omega
  calc M.edgeCount = ∑ i : Fin k, ∑ e : Sym2 V, C.col e i := h1
    _ ≤ ∑ i : Fin k, Fintype.card V / 2 := Finset.sum_le_sum (fun i _ => h2 i)
    _ = k * (Fintype.card V / 2) := by
        rw [Finset.sum_const_nat (s := (univ : Finset (Fin k)))
          (f := fun _ => Fintype.card V / 2) (m := Fintype.card V / 2) (fun _ _ => rfl)]
        simp

/-- `M` es **`k`-overfull**: más aristas (con multiplicidad) que `k·⌊n/2⌋`. -/
def IsOverfullWith (k : ℕ) : Prop := k * (Fintype.card V / 2) < M.edgeCount

/-- **Criterio overfull para multigrafos**: un multigrafo `k`-overfull no admite
ninguna coloración propia de aristas con `k` colores. -/
theorem not_edgeColorable_of_overfull {k : ℕ} (h : M.IsOverfullWith k) :
    ¬ Nonempty (M.EdgeColoring k) := by
  rintro ⟨C⟩
  have h1 := M.edgeCount_le_of_edgeColoring C
  unfold IsOverfullWith at h
  omega

/-- El multigrafo subyacente a un grafo simple. -/
def ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] : MultiGraph V where
  mult e := if e ∈ G.edgeSet then 1 else 0
  loopless e he := by
    have h : e ∉ G.edgeSet := fun hmem => G.not_isDiag_of_mem_edgeSet hmem he
    simp [h]

omit [DecidableEq V] in
/-- El multigrafo de un grafo simple tiene `|E(G)|` aristas. -/
theorem edgeCount_ofSimpleGraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    (ofSimpleGraph G).edgeCount = G.edgeFinset.card := by
  rw [edgeCount, ofSimpleGraph, ← Finset.card_filter]
  congr 1
  ext e
  simp [SimpleGraph.mem_edgeFinset]

/-- **Diana del caso general del hueco 1**: extensión multigrafo de un punto.
Existe un multigrafo lazo-libre `M` sobre `Option V`, con multiplicidades ≤ 2,
que contiene todas las aristas de `G` y es `Δ(G)`-regular.

Esta definición por sí sola no afirma existencia. En el caso saturado
casi regular basta la extensión simple del gate 3. Para déficit dos, el
gate 8 construye una extensión con multiplicidades a lo sumo dos; puede
necesitar aristas paralelas incidentes con el nuevo vértice. Fuera de la
saturación, unir al nuevo vértice todas las copias deficitarias no conserva
su grado máximo, y hace falta una construcción adicional. -/
def HasMultigraphExtension (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ M : MultiGraph (Option V),
    M.IsRegularOfDegree G.maxDegree ∧
      (∀ e : Sym2 (Option V), M.mult e ≤ 2) ∧
      (∀ u v : V, G.Adj u v → 1 ≤ M.mult (Sym2.mk (some u) (some v)))

#print axioms SimpleGraph.MultiGraph.sum_degrees_eq_twice_edgeCount
#print axioms SimpleGraph.MultiGraph.card_mul_of_regular
#print axioms SimpleGraph.MultiGraph.even_of_odd_card_of_regular
#print axioms SimpleGraph.MultiGraph.two_mul_sum_col_le
#print axioms SimpleGraph.MultiGraph.edgeCount_le_of_edgeColoring
#print axioms SimpleGraph.MultiGraph.not_edgeColorable_of_overfull

end MultiGraph

end SimpleGraph
