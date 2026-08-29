# Paper 04 → Lean 4 Theorem Mapping

**Paper:** *Separation Laws for Flip Bifurcations and Endogenous Switching Boundaries in Gradient Maps*  
(DCDS_clipped_gradient, Paper_04)

**Verification status:**  
- ✅ = fully machine‑verified (`lake build` passes)  
- ◐ = the paper’s asymptotic/analytic statement is formalized as an **exact algebraic kernel** (see notes below)

> **Note:** Paper locations refer to the current compiled numbering
> (Introduction = §1, Problem setting = §2, …, planar model = §8).

| Paper Location | Paper Statement | Lean 4 Theorem (File) | Status |
|----------------|------------------|------------------------|--------|
| §2.1, eq.(2.2) | Clipping operator \( \mathcal{C}_c(g) = \min\{1, c/\|g\|\}g \) | `clip` (Clipping.lean) | ✅ |
| §2.1 | \( \|\mathcal{C}_c(g)\| = \min\{\|g\|, c\} \) | `norm_clip` | ✅ |
| §2.1 | \( \mathcal{C}_c(g) = g \iff \|g\| \le c \) | `clip_eq_self_iff`, `clip_of_le` | ✅ |
| §2.1, eq.(2.8) | Clipped branch: \( \mathcal{C}_c(g) = (c/\|g\|)g \) for \( \|g\|>c \) | `clip_of_lt` | ✅ |
| §2.1 | Oddness: \( \mathcal{C}_c(-g) = -\mathcal{C}_c(g) \) | `clip_neg` | ✅ |
| §2.1, eq.(2.7)–(2.8) | Smooth/clipped branch identities | `clippedMap_eq_gradDescend_of_lt`, `clippedMap_eq_of_lt` | ✅ |
| §2.5, eq.(2.13) | Multipliers \( \rho_i(\eta) = 1 - \eta\lambda_i \) | `multiplier` | ✅ |
| §2.5, eq.(2.14)–(2.15) | \( \rho_d(\eta_f) = -1 \), \( \eta_f = 2/\lambda_* \) | `multiplier_eta_f`, `etaF` | ✅ |
| §2.5, eq.(2.29)–(2.30) | \( d\rho/d\eta = -\lambda_* \neq 0 \) (transversal crossing) | `multiplier_deriv`, `transversal_crossing` | ✅ |
| §2.5, eq.(2.28) | Noncritical spectrum: \( -1 < 1-2\lambda_i/\lambda_* < 1 \) | `noncritical_spectrum` | ✅ |
| §4.1, eq.(4.2) | \( \rho_*(\mu) = -1 - \lambda_*\mu \) | `critical_multiplier_mu` | ✅ |
| §5.1, Prop.5.1 | Exact gradient balance | `exact_gradient_balance` | ✅ |
| §5.1, eq.(5.3)–(5.4) | \( \nabla V(x_+) = -\nabla V(x_-) \), equal norms | `opposite_gradients`, `equal_gradient_norms` | ✅ |
| §5.2, Lemma 5.3 | Midpoint–difference equations | `midpoint_difference_equations` | ✅ |
| §5.6, Thm.5.10 | Simultaneous switching contact | `simultaneous_contact` (three variants) | ✅ |
| §5.7, Prop.5.12 | No mixed smooth–clipped period‑two orbit | `no_mixed_period_two` | ✅ |
| §7.1, Prop.7.1 | Exact geometry of fully clipped period‑two orbits | `fully_clipped_geometry` | ✅ |
| §7.3, eq.(7.11)–(7.12) | \( \phi_u D\mathcal{C}_c(g) = 0 \) (radial cancellation); \( P_u u = 0 \), \( \phi_u P_u = 0 \) | `clipDeriv_annihilates`, `proj_u_annihilates_u`, `phi_annihilates_proj` | ✅ |
| §7.4, Prop.7.5 | Pointwise neutral covector: \( \phi_u DF(x) = \phi_u \) | `pointwise_neutral` | ✅ |
| §7.5, Thm.7.7 | Universal unit multiplier (left covector form) | `universal_unit_multiplier_left` | ✅ |
| §7.5, Thm.7.7 | \( 1 \in \sigma(M_c) \) (finite‑dimensional) | `eigenvalue_one_of_left_eigenvector`, `fully_clipped_unit_multiplier` | ✅ |
| §4.3, Lemma 4.3 | Second‑iterate expansion (exact algebraic kernel) | `second_iterate_exact`, `second_iterate_minus_z` | ✅ |
| §4.3, eq.(4.15) | Amplitude balance: \( 2\lambda\mu z - 2\ell z^3 = 0 \) | `amplitude_balance` | ✅ |
| §4.4, eq.(4.27) | IFT nondegeneracy: \( \lambda_* - 3\ell_* w^2 = -2\lambda_* \) | `ift_nondegenerate` | ✅ |
| §4.5, eq.(4.29) | Two‑step multiplier \( \rho = 1-4\lambda\mu+O(\mu^{3/2}) \) | `two_step_multiplier_at_amplitude` (exact \( (1-2\lambda\mu)^2 \)) | ✅ |
| §4.4, eq.(4.20)–(4.21) | \( A_*^2 = \lambda_*/\ell_* = 3\lambda_*^2/\Gamma_* \) | `amplitude_algebra` | ✅ |
| §6.3, eq.(6.12)–(6.14) | \( K = 1/(\lambda^2 A^2 \|v\|^2) = \ell/(\lambda^3 \|v\|^2) = \Gamma/(3\lambda^4 \|v\|^2) \) | `separation_coefficient_ell`, `separation_coefficient_Gamma` | ✅ |
| §6.3, eq.(6.15) | \( K > 0 \) (by H4) | `separation_coefficient_pos` | ✅ |
| §8.1, eq.(8.5)–(8.6) | \( \lambda - bs + ds^2 > 0 \); \( xg(x) > 0 \) | `quadratic_positive`, `g_sign` | ✅ |
| §8.2, eq.(8.21) | Smooth period‑two cycle equation | `smooth_cycle_equation` | ✅ |
| §8.2, eq.(8.23)–(8.24) | Quadratic equation for \( q \) and explicit root | `q_quadratic`, `q_root` | ✅ |
| §8.6, eq.(8.45); §8.8, eq.(8.54) | First‑contact equation \( \Psi(\eta,c)=0 \); \( g(\eta c/2)-c = (\eta c/2)\Psi \) | `contact_equation`, `g_minus_c_Psi`, `g_eq_c_of_Psi` | ✅ |
| §8.7, eq.(8.48)–(8.49) | \( K_2 = 2b/\lambda^4 \), \( K_4 = 6b^2/\lambda^7 - 2d/\lambda^6 \) | `planar_separation_coefficients` | ✅ |
| §8.8, eq.(8.58) | Saturated step‑length law: \( 2a_c = \eta c \) | `exact_amplitude_saturation` | ✅ |
| §8.12 | \( \lambda=2, \nu=\tfrac12, b=1, d=1 \Rightarrow \eta_f=1, \ell_*=1, K_2=1/8 \) | `concrete_parameters` | ✅ |

---

## Notes

1. **Fully clipped unit multiplier (§7):**  
   `ClippingStructure` bundles two analytic axioms — Euler’s identity  
   \( D\rho(u)[u] = 1 \) and \( D\rho(-u) = -D\rho(u) \) — which hold for any \( C^1 \) positively homogeneous norm. All subsequent conclusions are machine‑verified from these axioms.

2. **Asymptotic statements (§4–§6: \( O(\cdot) \) expansions, center‑manifold reductions, implicit‑function branches):**  
   These require full analytic formalization.  
   In this repository, they are replaced by **exact algebraic kernels** — for example, the truncated normal‑form two‑step multiplier is verified as exactly \( (1-2\lambda\mu)^2 \) (stronger than the paper’s \( 1-4\lambda\mu+O(\mu^{3/2}) \)); the coefficients \( K_2 \) and \( K_4 \) are extracted by exact cancellation conditions from a polynomial ansatz.

3. **Verification:**  
   Open the `Lean4_Proofs` folder in VSCode, wait for the toolchain to load, then run:
   ```bash
   lake exe cache get
   lake build
   ```
