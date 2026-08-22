/- TOMBSTONE — soundness-hole witness (2026-08-22), REPAIRED same day.

   Before the repair, the following derivation of `False` compiled against
   the unhypothesized `adjoint_pi_spec` (no positivity assumption on π):

     π := (1, 0) on Fin 2,  A := (u₁, u₂) ↦ (u₂, 0),  u := δ₁, v := δ₂
     ⟨A†u, v⟩_π = π₂ · star((A†u) 2) · 1 = 0     (π₂ = 0)
     ⟨u, A v⟩_π = π₁ · star(1) · (Av) 1 = 1      (Aδ₂ = δ₁)
     spec ⟹ 0 = 1 ⟹ False

   `#print axioms inconsistency` reported:
     [propext, Classical.choice, Quot.sound,
      SGC.Axioms.GeometryGeneral.adjoint_pi,
      SGC.Axioms.GeometryGeneral.adjoint_pi_spec]

   REPAIR: `adjoint_pi_spec`, `adjoint_pi_involutive`, `adjoint_pi_comp`
   now require `(hπ : ∀ v, 0 < pi_dist v)`, under which the weighted
   adjoint `D_π⁻¹ A* D_π` is a model (satisfiable ⇒ consistent relative
   to a model). This file intentionally no longer contains the proof:
   it must NOT compile against the repaired axioms. To reproduce the
   historical derivation, check out the commit preceding the repair
   (see git log for "soundness repair") and restore this file from it.

   Lesson recorded in docs/axiom-discharge-campaign.md: axioms
   quantified over degenerate parameters are the primary inconsistency
   risk; the discharge campaign audits for satisfiability, not just
   usage. -/
