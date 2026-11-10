import R7.Spectral.Grouped
import R7.Certificates.Spectral.Slices.All
set_option Elab.async false

namespace R7.Core.SpectralCertificateTheorem
open R7.Core.MinorCertificates R7.Core.SpectralGrouped R7.Core.SpectralSlices R7.Core.Bivariate
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def entrySlice_0 : CertifiedSlice :=
 ⟨![0,0,0,12], R7.Core.SpectralSliceCertificates.Entry000.polynomial_0, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry000.polynomial_0 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry000.positive_0 y u hy⟩
noncomputable def entrySlice_1 : CertifiedSlice :=
 ⟨![0,0,1,11], R7.Core.SpectralSliceCertificates.Entry000.polynomial_1, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry000.polynomial_1 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry000.positive_1 y u hy⟩
noncomputable def entrySlice_2 : CertifiedSlice :=
 ⟨![0,0,2,10], R7.Core.SpectralSliceCertificates.Entry000.polynomial_2, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry000.polynomial_2 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry000.positive_2 y u hy⟩
noncomputable def entrySlice_3 : CertifiedSlice :=
 ⟨![0,0,3,9], R7.Core.SpectralSliceCertificates.Entry000.polynomial_3, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry000.polynomial_3 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry000.positive_3 y u hy⟩
noncomputable def entrySlice_4 : CertifiedSlice :=
 ⟨![0,0,4,8], R7.Core.SpectralSliceCertificates.Entry000.polynomial_4, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry000.polynomial_4 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry000.positive_4 y u hy⟩
noncomputable def entrySlice_5 : CertifiedSlice :=
 ⟨![0,0,5,7], R7.Core.SpectralSliceCertificates.Entry000.polynomial_5, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry000.polynomial_5 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry000.positive_5 y u hy⟩
noncomputable def entrySlice_6 : CertifiedSlice :=
 ⟨![0,0,6,6], R7.Core.SpectralSliceCertificates.Entry001.polynomial_6, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry001.polynomial_6 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry001.positive_6 y u hy⟩
noncomputable def entrySlice_7 : CertifiedSlice :=
 ⟨![0,0,7,5], R7.Core.SpectralSliceCertificates.Entry001.polynomial_7, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry001.polynomial_7 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry001.positive_7 y u hy⟩
noncomputable def entrySlice_8 : CertifiedSlice :=
 ⟨![0,0,8,4], R7.Core.SpectralSliceCertificates.Entry001.polynomial_8, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry001.polynomial_8 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry001.positive_8 y u hy⟩
noncomputable def entrySlice_9 : CertifiedSlice :=
 ⟨![0,0,9,3], R7.Core.SpectralSliceCertificates.Entry001.polynomial_9, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry001.polynomial_9 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry001.positive_9 y u hy⟩
noncomputable def entrySlice_10 : CertifiedSlice :=
 ⟨![0,0,10,2], R7.Core.SpectralSliceCertificates.Entry001.polynomial_10, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry001.polynomial_10 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry001.positive_10 y u hy⟩
noncomputable def entrySlice_11 : CertifiedSlice :=
 ⟨![0,0,11,1], R7.Core.SpectralSliceCertificates.Entry001.polynomial_11, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry001.polynomial_11 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry001.positive_11 y u hy⟩
noncomputable def entrySlice_12 : CertifiedSlice :=
 ⟨![0,0,12,0], R7.Core.SpectralSliceCertificates.Entry002.polynomial_12, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry002.polynomial_12 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry002.positive_12 y u hy⟩
noncomputable def entrySlice_13 : CertifiedSlice :=
 ⟨![0,1,0,11], R7.Core.SpectralSliceCertificates.Entry002.polynomial_13, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry002.polynomial_13 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry002.positive_13 y u hy⟩
noncomputable def entrySlice_14 : CertifiedSlice :=
 ⟨![0,1,1,10], R7.Core.SpectralSliceCertificates.Entry002.polynomial_14, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry002.polynomial_14 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry002.positive_14 y u hy⟩
noncomputable def entrySlice_15 : CertifiedSlice :=
 ⟨![0,1,2,9], R7.Core.SpectralSliceCertificates.Entry002.polynomial_15, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry002.polynomial_15 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry002.positive_15 y u hy⟩
noncomputable def entrySlice_16 : CertifiedSlice :=
 ⟨![0,1,3,8], R7.Core.SpectralSliceCertificates.Entry002.polynomial_16, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry002.polynomial_16 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry002.positive_16 y u hy⟩
noncomputable def entrySlice_17 : CertifiedSlice :=
 ⟨![0,1,4,7], R7.Core.SpectralSliceCertificates.Entry002.polynomial_17, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry002.polynomial_17 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry002.positive_17 y u hy⟩
noncomputable def entrySlice_18 : CertifiedSlice :=
 ⟨![0,1,5,6], R7.Core.SpectralSliceCertificates.Entry003.polynomial_18, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry003.polynomial_18 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry003.positive_18 y u hy⟩
noncomputable def entrySlice_19 : CertifiedSlice :=
 ⟨![0,1,6,5], R7.Core.SpectralSliceCertificates.Entry003.polynomial_19, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry003.polynomial_19 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry003.positive_19 y u hy⟩
noncomputable def entrySlice_20 : CertifiedSlice :=
 ⟨![0,1,7,4], R7.Core.SpectralSliceCertificates.Entry003.polynomial_20, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry003.polynomial_20 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry003.positive_20 y u hy⟩
noncomputable def entrySlice_21 : CertifiedSlice :=
 ⟨![0,1,8,3], R7.Core.SpectralSliceCertificates.Entry003.polynomial_21, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry003.polynomial_21 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry003.positive_21 y u hy⟩
noncomputable def entrySlice_22 : CertifiedSlice :=
 ⟨![0,1,9,2], R7.Core.SpectralSliceCertificates.Entry003.polynomial_22, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry003.polynomial_22 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry003.positive_22 y u hy⟩
noncomputable def entrySlice_23 : CertifiedSlice :=
 ⟨![0,1,10,1], R7.Core.SpectralSliceCertificates.Entry003.polynomial_23, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry003.polynomial_23 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry003.positive_23 y u hy⟩
noncomputable def entrySlice_24 : CertifiedSlice :=
 ⟨![0,1,11,0], R7.Core.SpectralSliceCertificates.Entry004.polynomial_24, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry004.polynomial_24 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry004.positive_24 y u hy⟩
noncomputable def entrySlice_25 : CertifiedSlice :=
 ⟨![0,2,0,10], R7.Core.SpectralSliceCertificates.Entry004.polynomial_25, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry004.polynomial_25 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry004.positive_25 y u hy⟩
noncomputable def entrySlice_26 : CertifiedSlice :=
 ⟨![0,2,1,9], R7.Core.SpectralSliceCertificates.Entry004.polynomial_26, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry004.polynomial_26 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry004.positive_26 y u hy⟩
noncomputable def entrySlice_27 : CertifiedSlice :=
 ⟨![0,2,2,8], R7.Core.SpectralSliceCertificates.Entry004.polynomial_27, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry004.polynomial_27 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry004.positive_27 y u hy⟩
noncomputable def entrySlice_28 : CertifiedSlice :=
 ⟨![0,2,3,7], R7.Core.SpectralSliceCertificates.Entry004.polynomial_28, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry004.polynomial_28 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry004.positive_28 y u hy⟩
noncomputable def entrySlice_29 : CertifiedSlice :=
 ⟨![0,2,4,6], R7.Core.SpectralSliceCertificates.Entry004.polynomial_29, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry004.polynomial_29 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry004.positive_29 y u hy⟩
noncomputable def entrySlice_30 : CertifiedSlice :=
 ⟨![0,2,5,5], R7.Core.SpectralSliceCertificates.Entry005.polynomial_30, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry005.polynomial_30 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry005.positive_30 y u hy⟩
noncomputable def entrySlice_31 : CertifiedSlice :=
 ⟨![0,2,6,4], R7.Core.SpectralSliceCertificates.Entry005.polynomial_31, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry005.polynomial_31 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry005.positive_31 y u hy⟩
noncomputable def entrySlice_32 : CertifiedSlice :=
 ⟨![0,2,7,3], R7.Core.SpectralSliceCertificates.Entry005.polynomial_32, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry005.polynomial_32 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry005.positive_32 y u hy⟩
noncomputable def entrySlice_33 : CertifiedSlice :=
 ⟨![0,2,8,2], R7.Core.SpectralSliceCertificates.Entry005.polynomial_33, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry005.polynomial_33 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry005.positive_33 y u hy⟩
noncomputable def entrySlice_34 : CertifiedSlice :=
 ⟨![0,2,9,1], R7.Core.SpectralSliceCertificates.Entry005.polynomial_34, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry005.polynomial_34 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry005.positive_34 y u hy⟩
noncomputable def entrySlice_35 : CertifiedSlice :=
 ⟨![0,2,10,0], R7.Core.SpectralSliceCertificates.Entry005.polynomial_35, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry005.polynomial_35 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry005.positive_35 y u hy⟩
noncomputable def entrySlice_36 : CertifiedSlice :=
 ⟨![0,3,0,9], R7.Core.SpectralSliceCertificates.Entry006.polynomial_36, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry006.polynomial_36 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry006.positive_36 y u hy⟩
noncomputable def entrySlice_37 : CertifiedSlice :=
 ⟨![0,3,1,8], R7.Core.SpectralSliceCertificates.Entry006.polynomial_37, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry006.polynomial_37 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry006.positive_37 y u hy⟩
noncomputable def entrySlice_38 : CertifiedSlice :=
 ⟨![0,3,2,7], R7.Core.SpectralSliceCertificates.Entry006.polynomial_38, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry006.polynomial_38 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry006.positive_38 y u hy⟩
noncomputable def entrySlice_39 : CertifiedSlice :=
 ⟨![0,3,3,6], R7.Core.SpectralSliceCertificates.Entry006.polynomial_39, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry006.polynomial_39 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry006.positive_39 y u hy⟩
noncomputable def entrySlice_40 : CertifiedSlice :=
 ⟨![0,3,4,5], R7.Core.SpectralSliceCertificates.Entry006.polynomial_40, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry006.polynomial_40 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry006.positive_40 y u hy⟩
noncomputable def entrySlice_41 : CertifiedSlice :=
 ⟨![0,3,5,4], R7.Core.SpectralSliceCertificates.Entry006.polynomial_41, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry006.polynomial_41 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry006.positive_41 y u hy⟩
noncomputable def entrySlice_42 : CertifiedSlice :=
 ⟨![0,3,6,3], R7.Core.SpectralSliceCertificates.Entry007.polynomial_42, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry007.polynomial_42 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry007.positive_42 y u hy⟩
noncomputable def entrySlice_43 : CertifiedSlice :=
 ⟨![0,3,7,2], R7.Core.SpectralSliceCertificates.Entry007.polynomial_43, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry007.polynomial_43 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry007.positive_43 y u hy⟩
noncomputable def entrySlice_44 : CertifiedSlice :=
 ⟨![0,3,8,1], R7.Core.SpectralSliceCertificates.Entry007.polynomial_44, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry007.polynomial_44 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry007.positive_44 y u hy⟩
noncomputable def entrySlice_45 : CertifiedSlice :=
 ⟨![0,3,9,0], R7.Core.SpectralSliceCertificates.Entry007.polynomial_45, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry007.polynomial_45 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry007.positive_45 y u hy⟩
noncomputable def entrySlice_46 : CertifiedSlice :=
 ⟨![0,4,0,8], R7.Core.SpectralSliceCertificates.Entry007.polynomial_46, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry007.polynomial_46 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry007.positive_46 y u hy⟩
noncomputable def entrySlice_47 : CertifiedSlice :=
 ⟨![0,4,1,7], R7.Core.SpectralSliceCertificates.Entry007.polynomial_47, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry007.polynomial_47 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry007.positive_47 y u hy⟩
noncomputable def entrySlice_48 : CertifiedSlice :=
 ⟨![0,4,2,6], R7.Core.SpectralSliceCertificates.Entry008.polynomial_48, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry008.polynomial_48 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry008.positive_48 y u hy⟩
noncomputable def entrySlice_49 : CertifiedSlice :=
 ⟨![0,4,3,5], R7.Core.SpectralSliceCertificates.Entry008.polynomial_49, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry008.polynomial_49 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry008.positive_49 y u hy⟩
noncomputable def entrySlice_50 : CertifiedSlice :=
 ⟨![0,4,4,4], R7.Core.SpectralSliceCertificates.Entry008.polynomial_50, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry008.polynomial_50 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry008.positive_50 y u hy⟩
noncomputable def entrySlice_51 : CertifiedSlice :=
 ⟨![0,4,5,3], R7.Core.SpectralSliceCertificates.Entry008.polynomial_51, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry008.polynomial_51 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry008.positive_51 y u hy⟩
noncomputable def entrySlice_52 : CertifiedSlice :=
 ⟨![0,4,6,2], R7.Core.SpectralSliceCertificates.Entry008.polynomial_52, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry008.polynomial_52 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry008.positive_52 y u hy⟩
noncomputable def entrySlice_53 : CertifiedSlice :=
 ⟨![0,4,7,1], R7.Core.SpectralSliceCertificates.Entry008.polynomial_53, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry008.polynomial_53 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry008.positive_53 y u hy⟩
noncomputable def entrySlice_54 : CertifiedSlice :=
 ⟨![0,4,8,0], R7.Core.SpectralSliceCertificates.Entry009.polynomial_54, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry009.polynomial_54 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry009.positive_54 y u hy⟩
noncomputable def entrySlice_55 : CertifiedSlice :=
 ⟨![0,5,0,7], R7.Core.SpectralSliceCertificates.Entry009.polynomial_55, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry009.polynomial_55 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry009.positive_55 y u hy⟩
noncomputable def entrySlice_56 : CertifiedSlice :=
 ⟨![0,5,1,6], R7.Core.SpectralSliceCertificates.Entry009.polynomial_56, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry009.polynomial_56 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry009.positive_56 y u hy⟩
noncomputable def entrySlice_57 : CertifiedSlice :=
 ⟨![0,5,2,5], R7.Core.SpectralSliceCertificates.Entry009.polynomial_57, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry009.polynomial_57 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry009.positive_57 y u hy⟩
noncomputable def entrySlice_58 : CertifiedSlice :=
 ⟨![0,5,3,4], R7.Core.SpectralSliceCertificates.Entry009.polynomial_58, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry009.polynomial_58 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry009.positive_58 y u hy⟩
noncomputable def entrySlice_59 : CertifiedSlice :=
 ⟨![0,5,4,3], R7.Core.SpectralSliceCertificates.Entry009.polynomial_59, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry009.polynomial_59 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry009.positive_59 y u hy⟩
noncomputable def entrySlice_60 : CertifiedSlice :=
 ⟨![0,5,5,2], R7.Core.SpectralSliceCertificates.Entry010.polynomial_60, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry010.polynomial_60 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry010.positive_60 y u hy⟩
noncomputable def entrySlice_61 : CertifiedSlice :=
 ⟨![0,5,6,1], R7.Core.SpectralSliceCertificates.Entry010.polynomial_61, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry010.polynomial_61 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry010.positive_61 y u hy⟩
noncomputable def entrySlice_62 : CertifiedSlice :=
 ⟨![0,5,7,0], R7.Core.SpectralSliceCertificates.Entry010.polynomial_62, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry010.polynomial_62 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry010.positive_62 y u hy⟩
noncomputable def entrySlice_63 : CertifiedSlice :=
 ⟨![0,6,0,6], R7.Core.SpectralSliceCertificates.Entry010.polynomial_63, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry010.polynomial_63 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry010.positive_63 y u hy⟩
noncomputable def entrySlice_64 : CertifiedSlice :=
 ⟨![0,6,1,5], R7.Core.SpectralSliceCertificates.Entry010.polynomial_64, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry010.polynomial_64 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry010.positive_64 y u hy⟩
noncomputable def entrySlice_65 : CertifiedSlice :=
 ⟨![0,6,2,4], R7.Core.SpectralSliceCertificates.Entry010.polynomial_65, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry010.polynomial_65 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry010.positive_65 y u hy⟩
noncomputable def entrySlice_66 : CertifiedSlice :=
 ⟨![0,6,3,3], R7.Core.SpectralSliceCertificates.Entry011.polynomial_66, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry011.polynomial_66 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry011.positive_66 y u hy⟩
noncomputable def entrySlice_67 : CertifiedSlice :=
 ⟨![0,6,4,2], R7.Core.SpectralSliceCertificates.Entry011.polynomial_67, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry011.polynomial_67 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry011.positive_67 y u hy⟩
noncomputable def entrySlice_68 : CertifiedSlice :=
 ⟨![0,6,5,1], R7.Core.SpectralSliceCertificates.Entry011.polynomial_68, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry011.polynomial_68 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry011.positive_68 y u hy⟩
noncomputable def entrySlice_69 : CertifiedSlice :=
 ⟨![0,6,6,0], R7.Core.SpectralSliceCertificates.Entry011.polynomial_69, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry011.polynomial_69 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry011.positive_69 y u hy⟩
noncomputable def entrySlice_70 : CertifiedSlice :=
 ⟨![0,7,0,5], R7.Core.SpectralSliceCertificates.Entry011.polynomial_70, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry011.polynomial_70 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry011.positive_70 y u hy⟩
noncomputable def entrySlice_71 : CertifiedSlice :=
 ⟨![0,7,1,4], R7.Core.SpectralSliceCertificates.Entry011.polynomial_71, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry011.polynomial_71 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry011.positive_71 y u hy⟩
noncomputable def entrySlice_72 : CertifiedSlice :=
 ⟨![0,7,2,3], R7.Core.SpectralSliceCertificates.Entry012.polynomial_72, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry012.polynomial_72 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry012.positive_72 y u hy⟩
noncomputable def entrySlice_73 : CertifiedSlice :=
 ⟨![0,7,3,2], R7.Core.SpectralSliceCertificates.Entry012.polynomial_73, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry012.polynomial_73 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry012.positive_73 y u hy⟩
noncomputable def entrySlice_74 : CertifiedSlice :=
 ⟨![0,7,4,1], R7.Core.SpectralSliceCertificates.Entry012.polynomial_74, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry012.polynomial_74 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry012.positive_74 y u hy⟩
noncomputable def entrySlice_75 : CertifiedSlice :=
 ⟨![0,8,0,4], R7.Core.SpectralSliceCertificates.Entry012.polynomial_75, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry012.polynomial_75 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry012.positive_75 y u hy⟩
noncomputable def entrySlice_76 : CertifiedSlice :=
 ⟨![0,8,1,3], R7.Core.SpectralSliceCertificates.Entry012.polynomial_76, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry012.polynomial_76 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry012.positive_76 y u hy⟩
noncomputable def entrySlice_77 : CertifiedSlice :=
 ⟨![0,8,2,2], R7.Core.SpectralSliceCertificates.Entry012.polynomial_77, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry012.polynomial_77 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry012.positive_77 y u hy⟩
noncomputable def entrySlice_78 : CertifiedSlice :=
 ⟨![0,8,3,1], R7.Core.SpectralSliceCertificates.Entry013.polynomial_78, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry013.polynomial_78 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry013.positive_78 y u hy⟩
noncomputable def entrySlice_79 : CertifiedSlice :=
 ⟨![0,9,0,3], R7.Core.SpectralSliceCertificates.Entry013.polynomial_79, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry013.polynomial_79 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry013.positive_79 y u hy⟩
noncomputable def entrySlice_80 : CertifiedSlice :=
 ⟨![0,9,1,2], R7.Core.SpectralSliceCertificates.Entry013.polynomial_80, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry013.polynomial_80 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry013.positive_80 y u hy⟩
noncomputable def entrySlice_81 : CertifiedSlice :=
 ⟨![0,9,2,1], R7.Core.SpectralSliceCertificates.Entry013.polynomial_81, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry013.polynomial_81 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry013.positive_81 y u hy⟩
noncomputable def entrySlice_82 : CertifiedSlice :=
 ⟨![0,10,0,2], R7.Core.SpectralSliceCertificates.Entry013.polynomial_82, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry013.polynomial_82 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry013.positive_82 y u hy⟩
noncomputable def entrySlice_83 : CertifiedSlice :=
 ⟨![0,10,1,1], R7.Core.SpectralSliceCertificates.Entry013.polynomial_83, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry013.polynomial_83 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry013.positive_83 y u hy⟩
noncomputable def entrySlice_84 : CertifiedSlice :=
 ⟨![0,11,0,1], R7.Core.SpectralSliceCertificates.Entry014.polynomial_84, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry014.polynomial_84 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry014.positive_84 y u hy⟩
noncomputable def entrySlice_85 : CertifiedSlice :=
 ⟨![1,0,0,11], R7.Core.SpectralSliceCertificates.Entry014.polynomial_85, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry014.polynomial_85 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry014.positive_85 y u hy⟩
noncomputable def entrySlice_86 : CertifiedSlice :=
 ⟨![1,0,1,10], R7.Core.SpectralSliceCertificates.Entry014.polynomial_86, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry014.polynomial_86 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry014.positive_86 y u hy⟩
noncomputable def entrySlice_87 : CertifiedSlice :=
 ⟨![1,0,2,9], R7.Core.SpectralSliceCertificates.Entry014.polynomial_87, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry014.polynomial_87 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry014.positive_87 y u hy⟩
noncomputable def entrySlice_88 : CertifiedSlice :=
 ⟨![1,0,3,8], R7.Core.SpectralSliceCertificates.Entry014.polynomial_88, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry014.polynomial_88 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry014.positive_88 y u hy⟩
noncomputable def entrySlice_89 : CertifiedSlice :=
 ⟨![1,0,4,7], R7.Core.SpectralSliceCertificates.Entry014.polynomial_89, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry014.polynomial_89 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry014.positive_89 y u hy⟩
noncomputable def entrySlice_90 : CertifiedSlice :=
 ⟨![1,0,5,6], R7.Core.SpectralSliceCertificates.Entry015.polynomial_90, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry015.polynomial_90 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry015.positive_90 y u hy⟩
noncomputable def entrySlice_91 : CertifiedSlice :=
 ⟨![1,0,6,5], R7.Core.SpectralSliceCertificates.Entry015.polynomial_91, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry015.polynomial_91 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry015.positive_91 y u hy⟩
noncomputable def entrySlice_92 : CertifiedSlice :=
 ⟨![1,0,7,4], R7.Core.SpectralSliceCertificates.Entry015.polynomial_92, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry015.polynomial_92 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry015.positive_92 y u hy⟩
noncomputable def entrySlice_93 : CertifiedSlice :=
 ⟨![1,0,8,3], R7.Core.SpectralSliceCertificates.Entry015.polynomial_93, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry015.polynomial_93 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry015.positive_93 y u hy⟩
noncomputable def entrySlice_94 : CertifiedSlice :=
 ⟨![1,0,9,2], R7.Core.SpectralSliceCertificates.Entry015.polynomial_94, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry015.polynomial_94 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry015.positive_94 y u hy⟩
noncomputable def entrySlice_95 : CertifiedSlice :=
 ⟨![1,0,10,1], R7.Core.SpectralSliceCertificates.Entry015.polynomial_95, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry015.polynomial_95 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry015.positive_95 y u hy⟩
noncomputable def entrySlice_96 : CertifiedSlice :=
 ⟨![1,1,0,10], R7.Core.SpectralSliceCertificates.Entry016.polynomial_96, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry016.polynomial_96 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry016.positive_96 y u hy⟩
noncomputable def entrySlice_97 : CertifiedSlice :=
 ⟨![1,1,1,9], R7.Core.SpectralSliceCertificates.Entry016.polynomial_97, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry016.polynomial_97 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry016.positive_97 y u hy⟩
noncomputable def entrySlice_98 : CertifiedSlice :=
 ⟨![1,1,2,8], R7.Core.SpectralSliceCertificates.Entry016.polynomial_98, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry016.polynomial_98 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry016.positive_98 y u hy⟩
noncomputable def entrySlice_99 : CertifiedSlice :=
 ⟨![1,1,3,7], R7.Core.SpectralSliceCertificates.Entry016.polynomial_99, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry016.polynomial_99 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry016.positive_99 y u hy⟩
noncomputable def entrySlice_100 : CertifiedSlice :=
 ⟨![1,1,4,6], R7.Core.SpectralSliceCertificates.Entry016.polynomial_100, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry016.polynomial_100 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry016.positive_100 y u hy⟩
noncomputable def entrySlice_101 : CertifiedSlice :=
 ⟨![1,1,5,5], R7.Core.SpectralSliceCertificates.Entry016.polynomial_101, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry016.polynomial_101 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry016.positive_101 y u hy⟩
noncomputable def entrySlice_102 : CertifiedSlice :=
 ⟨![1,1,6,4], R7.Core.SpectralSliceCertificates.Entry017.polynomial_102, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry017.polynomial_102 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry017.positive_102 y u hy⟩
noncomputable def entrySlice_103 : CertifiedSlice :=
 ⟨![1,1,7,3], R7.Core.SpectralSliceCertificates.Entry017.polynomial_103, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry017.polynomial_103 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry017.positive_103 y u hy⟩
noncomputable def entrySlice_104 : CertifiedSlice :=
 ⟨![1,1,8,2], R7.Core.SpectralSliceCertificates.Entry017.polynomial_104, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry017.polynomial_104 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry017.positive_104 y u hy⟩
noncomputable def entrySlice_105 : CertifiedSlice :=
 ⟨![1,1,9,1], R7.Core.SpectralSliceCertificates.Entry017.polynomial_105, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry017.polynomial_105 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry017.positive_105 y u hy⟩
noncomputable def entrySlice_106 : CertifiedSlice :=
 ⟨![1,2,0,9], R7.Core.SpectralSliceCertificates.Entry017.polynomial_106, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry017.polynomial_106 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry017.positive_106 y u hy⟩
noncomputable def entrySlice_107 : CertifiedSlice :=
 ⟨![1,2,1,8], R7.Core.SpectralSliceCertificates.Entry017.polynomial_107, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry017.polynomial_107 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry017.positive_107 y u hy⟩
noncomputable def entrySlice_108 : CertifiedSlice :=
 ⟨![1,2,2,7], R7.Core.SpectralSliceCertificates.Entry018.polynomial_108, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry018.polynomial_108 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry018.positive_108 y u hy⟩
noncomputable def entrySlice_109 : CertifiedSlice :=
 ⟨![1,2,3,6], R7.Core.SpectralSliceCertificates.Entry018.polynomial_109, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry018.polynomial_109 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry018.positive_109 y u hy⟩
noncomputable def entrySlice_110 : CertifiedSlice :=
 ⟨![1,2,4,5], R7.Core.SpectralSliceCertificates.Entry018.polynomial_110, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry018.polynomial_110 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry018.positive_110 y u hy⟩
noncomputable def entrySlice_111 : CertifiedSlice :=
 ⟨![1,2,5,4], R7.Core.SpectralSliceCertificates.Entry018.polynomial_111, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry018.polynomial_111 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry018.positive_111 y u hy⟩
noncomputable def entrySlice_112 : CertifiedSlice :=
 ⟨![1,2,6,3], R7.Core.SpectralSliceCertificates.Entry018.polynomial_112, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry018.polynomial_112 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry018.positive_112 y u hy⟩
noncomputable def entrySlice_113 : CertifiedSlice :=
 ⟨![1,2,7,2], R7.Core.SpectralSliceCertificates.Entry018.polynomial_113, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry018.polynomial_113 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry018.positive_113 y u hy⟩
noncomputable def entrySlice_114 : CertifiedSlice :=
 ⟨![1,2,8,1], R7.Core.SpectralSliceCertificates.Entry019.polynomial_114, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry019.polynomial_114 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry019.positive_114 y u hy⟩
noncomputable def entrySlice_115 : CertifiedSlice :=
 ⟨![1,3,0,8], R7.Core.SpectralSliceCertificates.Entry019.polynomial_115, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry019.polynomial_115 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry019.positive_115 y u hy⟩
noncomputable def entrySlice_116 : CertifiedSlice :=
 ⟨![1,3,1,7], R7.Core.SpectralSliceCertificates.Entry019.polynomial_116, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry019.polynomial_116 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry019.positive_116 y u hy⟩
noncomputable def entrySlice_117 : CertifiedSlice :=
 ⟨![1,3,2,6], R7.Core.SpectralSliceCertificates.Entry019.polynomial_117, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry019.polynomial_117 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry019.positive_117 y u hy⟩
noncomputable def entrySlice_118 : CertifiedSlice :=
 ⟨![1,3,3,5], R7.Core.SpectralSliceCertificates.Entry019.polynomial_118, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry019.polynomial_118 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry019.positive_118 y u hy⟩
noncomputable def entrySlice_119 : CertifiedSlice :=
 ⟨![1,3,4,4], R7.Core.SpectralSliceCertificates.Entry019.polynomial_119, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry019.polynomial_119 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry019.positive_119 y u hy⟩
noncomputable def entrySlice_120 : CertifiedSlice :=
 ⟨![1,3,5,3], R7.Core.SpectralSliceCertificates.Entry020.polynomial_120, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry020.polynomial_120 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry020.positive_120 y u hy⟩
noncomputable def entrySlice_121 : CertifiedSlice :=
 ⟨![1,3,6,2], R7.Core.SpectralSliceCertificates.Entry020.polynomial_121, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry020.polynomial_121 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry020.positive_121 y u hy⟩
noncomputable def entrySlice_122 : CertifiedSlice :=
 ⟨![1,3,7,1], R7.Core.SpectralSliceCertificates.Entry020.polynomial_122, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry020.polynomial_122 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry020.positive_122 y u hy⟩
noncomputable def entrySlice_123 : CertifiedSlice :=
 ⟨![1,4,0,7], R7.Core.SpectralSliceCertificates.Entry020.polynomial_123, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry020.polynomial_123 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry020.positive_123 y u hy⟩
noncomputable def entrySlice_124 : CertifiedSlice :=
 ⟨![1,4,1,6], R7.Core.SpectralSliceCertificates.Entry020.polynomial_124, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry020.polynomial_124 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry020.positive_124 y u hy⟩
noncomputable def entrySlice_125 : CertifiedSlice :=
 ⟨![1,4,2,5], R7.Core.SpectralSliceCertificates.Entry020.polynomial_125, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry020.polynomial_125 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry020.positive_125 y u hy⟩
noncomputable def entrySlice_126 : CertifiedSlice :=
 ⟨![1,4,3,4], R7.Core.SpectralSliceCertificates.Entry021.polynomial_126, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry021.polynomial_126 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry021.positive_126 y u hy⟩
noncomputable def entrySlice_127 : CertifiedSlice :=
 ⟨![1,4,4,3], R7.Core.SpectralSliceCertificates.Entry021.polynomial_127, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry021.polynomial_127 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry021.positive_127 y u hy⟩
noncomputable def entrySlice_128 : CertifiedSlice :=
 ⟨![1,4,5,2], R7.Core.SpectralSliceCertificates.Entry021.polynomial_128, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry021.polynomial_128 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry021.positive_128 y u hy⟩
noncomputable def entrySlice_129 : CertifiedSlice :=
 ⟨![1,4,6,1], R7.Core.SpectralSliceCertificates.Entry021.polynomial_129, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry021.polynomial_129 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry021.positive_129 y u hy⟩
noncomputable def entrySlice_130 : CertifiedSlice :=
 ⟨![1,5,0,6], R7.Core.SpectralSliceCertificates.Entry021.polynomial_130, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry021.polynomial_130 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry021.positive_130 y u hy⟩
noncomputable def entrySlice_131 : CertifiedSlice :=
 ⟨![1,5,1,5], R7.Core.SpectralSliceCertificates.Entry021.polynomial_131, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry021.polynomial_131 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry021.positive_131 y u hy⟩
noncomputable def entrySlice_132 : CertifiedSlice :=
 ⟨![1,5,2,4], R7.Core.SpectralSliceCertificates.Entry022.polynomial_132, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry022.polynomial_132 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry022.positive_132 y u hy⟩
noncomputable def entrySlice_133 : CertifiedSlice :=
 ⟨![1,5,3,3], R7.Core.SpectralSliceCertificates.Entry022.polynomial_133, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry022.polynomial_133 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry022.positive_133 y u hy⟩
noncomputable def entrySlice_134 : CertifiedSlice :=
 ⟨![1,5,4,2], R7.Core.SpectralSliceCertificates.Entry022.polynomial_134, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry022.polynomial_134 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry022.positive_134 y u hy⟩
noncomputable def entrySlice_135 : CertifiedSlice :=
 ⟨![1,5,5,1], R7.Core.SpectralSliceCertificates.Entry022.polynomial_135, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry022.polynomial_135 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry022.positive_135 y u hy⟩
noncomputable def entrySlice_136 : CertifiedSlice :=
 ⟨![1,6,0,5], R7.Core.SpectralSliceCertificates.Entry022.polynomial_136, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry022.polynomial_136 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry022.positive_136 y u hy⟩
noncomputable def entrySlice_137 : CertifiedSlice :=
 ⟨![1,6,1,4], R7.Core.SpectralSliceCertificates.Entry022.polynomial_137, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry022.polynomial_137 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry022.positive_137 y u hy⟩
noncomputable def entrySlice_138 : CertifiedSlice :=
 ⟨![1,6,2,3], R7.Core.SpectralSliceCertificates.Entry023.polynomial_138, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry023.polynomial_138 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry023.positive_138 y u hy⟩
noncomputable def entrySlice_139 : CertifiedSlice :=
 ⟨![1,6,3,2], R7.Core.SpectralSliceCertificates.Entry023.polynomial_139, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry023.polynomial_139 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry023.positive_139 y u hy⟩
noncomputable def entrySlice_140 : CertifiedSlice :=
 ⟨![1,7,0,4], R7.Core.SpectralSliceCertificates.Entry023.polynomial_140, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry023.polynomial_140 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry023.positive_140 y u hy⟩
noncomputable def entrySlice_141 : CertifiedSlice :=
 ⟨![1,7,1,3], R7.Core.SpectralSliceCertificates.Entry023.polynomial_141, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry023.polynomial_141 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry023.positive_141 y u hy⟩
noncomputable def entrySlice_142 : CertifiedSlice :=
 ⟨![1,7,2,2], R7.Core.SpectralSliceCertificates.Entry023.polynomial_142, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry023.polynomial_142 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry023.positive_142 y u hy⟩
noncomputable def entrySlice_143 : CertifiedSlice :=
 ⟨![1,8,0,3], R7.Core.SpectralSliceCertificates.Entry023.polynomial_143, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry023.polynomial_143 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry023.positive_143 y u hy⟩
noncomputable def entrySlice_144 : CertifiedSlice :=
 ⟨![1,8,1,2], R7.Core.SpectralSliceCertificates.Entry024.polynomial_144, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry024.polynomial_144 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry024.positive_144 y u hy⟩
noncomputable def entrySlice_145 : CertifiedSlice :=
 ⟨![1,9,0,2], R7.Core.SpectralSliceCertificates.Entry024.polynomial_145, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry024.polynomial_145 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry024.positive_145 y u hy⟩
noncomputable def entrySlice_146 : CertifiedSlice :=
 ⟨![2,0,0,10], R7.Core.SpectralSliceCertificates.Entry024.polynomial_146, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry024.polynomial_146 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry024.positive_146 y u hy⟩
noncomputable def entrySlice_147 : CertifiedSlice :=
 ⟨![2,0,1,9], R7.Core.SpectralSliceCertificates.Entry024.polynomial_147, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry024.polynomial_147 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry024.positive_147 y u hy⟩
noncomputable def entrySlice_148 : CertifiedSlice :=
 ⟨![2,0,2,8], R7.Core.SpectralSliceCertificates.Entry024.polynomial_148, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry024.polynomial_148 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry024.positive_148 y u hy⟩
noncomputable def entrySlice_149 : CertifiedSlice :=
 ⟨![2,0,3,7], R7.Core.SpectralSliceCertificates.Entry024.polynomial_149, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry024.polynomial_149 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry024.positive_149 y u hy⟩
noncomputable def entrySlice_150 : CertifiedSlice :=
 ⟨![2,0,4,6], R7.Core.SpectralSliceCertificates.Entry025.polynomial_150, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry025.polynomial_150 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry025.positive_150 y u hy⟩
noncomputable def entrySlice_151 : CertifiedSlice :=
 ⟨![2,0,5,5], R7.Core.SpectralSliceCertificates.Entry025.polynomial_151, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry025.polynomial_151 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry025.positive_151 y u hy⟩
noncomputable def entrySlice_152 : CertifiedSlice :=
 ⟨![2,0,6,4], R7.Core.SpectralSliceCertificates.Entry025.polynomial_152, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry025.polynomial_152 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry025.positive_152 y u hy⟩
noncomputable def entrySlice_153 : CertifiedSlice :=
 ⟨![2,0,7,3], R7.Core.SpectralSliceCertificates.Entry025.polynomial_153, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry025.polynomial_153 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry025.positive_153 y u hy⟩
noncomputable def entrySlice_154 : CertifiedSlice :=
 ⟨![2,0,8,2], R7.Core.SpectralSliceCertificates.Entry025.polynomial_154, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry025.polynomial_154 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry025.positive_154 y u hy⟩
noncomputable def entrySlice_155 : CertifiedSlice :=
 ⟨![2,1,0,9], R7.Core.SpectralSliceCertificates.Entry025.polynomial_155, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry025.polynomial_155 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry025.positive_155 y u hy⟩
noncomputable def entrySlice_156 : CertifiedSlice :=
 ⟨![2,1,1,8], R7.Core.SpectralSliceCertificates.Entry026.polynomial_156, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry026.polynomial_156 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry026.positive_156 y u hy⟩
noncomputable def entrySlice_157 : CertifiedSlice :=
 ⟨![2,1,2,7], R7.Core.SpectralSliceCertificates.Entry026.polynomial_157, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry026.polynomial_157 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry026.positive_157 y u hy⟩
noncomputable def entrySlice_158 : CertifiedSlice :=
 ⟨![2,1,3,6], R7.Core.SpectralSliceCertificates.Entry026.polynomial_158, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry026.polynomial_158 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry026.positive_158 y u hy⟩
noncomputable def entrySlice_159 : CertifiedSlice :=
 ⟨![2,1,4,5], R7.Core.SpectralSliceCertificates.Entry026.polynomial_159, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry026.polynomial_159 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry026.positive_159 y u hy⟩
noncomputable def entrySlice_160 : CertifiedSlice :=
 ⟨![2,1,5,4], R7.Core.SpectralSliceCertificates.Entry026.polynomial_160, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry026.polynomial_160 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry026.positive_160 y u hy⟩
noncomputable def entrySlice_161 : CertifiedSlice :=
 ⟨![2,1,6,3], R7.Core.SpectralSliceCertificates.Entry026.polynomial_161, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry026.polynomial_161 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry026.positive_161 y u hy⟩
noncomputable def entrySlice_162 : CertifiedSlice :=
 ⟨![2,1,7,2], R7.Core.SpectralSliceCertificates.Entry027.polynomial_162, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry027.polynomial_162 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry027.positive_162 y u hy⟩
noncomputable def entrySlice_163 : CertifiedSlice :=
 ⟨![2,2,0,8], R7.Core.SpectralSliceCertificates.Entry027.polynomial_163, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry027.polynomial_163 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry027.positive_163 y u hy⟩
noncomputable def entrySlice_164 : CertifiedSlice :=
 ⟨![2,2,1,7], R7.Core.SpectralSliceCertificates.Entry027.polynomial_164, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry027.polynomial_164 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry027.positive_164 y u hy⟩
noncomputable def entrySlice_165 : CertifiedSlice :=
 ⟨![2,2,2,6], R7.Core.SpectralSliceCertificates.Entry027.polynomial_165, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry027.polynomial_165 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry027.positive_165 y u hy⟩
noncomputable def entrySlice_166 : CertifiedSlice :=
 ⟨![2,2,3,5], R7.Core.SpectralSliceCertificates.Entry027.polynomial_166, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry027.polynomial_166 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry027.positive_166 y u hy⟩
noncomputable def entrySlice_167 : CertifiedSlice :=
 ⟨![2,2,4,4], R7.Core.SpectralSliceCertificates.Entry027.polynomial_167, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry027.polynomial_167 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry027.positive_167 y u hy⟩
noncomputable def entrySlice_168 : CertifiedSlice :=
 ⟨![2,2,5,3], R7.Core.SpectralSliceCertificates.Entry028.polynomial_168, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry028.polynomial_168 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry028.positive_168 y u hy⟩
noncomputable def entrySlice_169 : CertifiedSlice :=
 ⟨![2,2,6,2], R7.Core.SpectralSliceCertificates.Entry028.polynomial_169, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry028.polynomial_169 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry028.positive_169 y u hy⟩
noncomputable def entrySlice_170 : CertifiedSlice :=
 ⟨![2,3,0,7], R7.Core.SpectralSliceCertificates.Entry028.polynomial_170, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry028.polynomial_170 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry028.positive_170 y u hy⟩
noncomputable def entrySlice_171 : CertifiedSlice :=
 ⟨![2,3,1,6], R7.Core.SpectralSliceCertificates.Entry028.polynomial_171, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry028.polynomial_171 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry028.positive_171 y u hy⟩
noncomputable def entrySlice_172 : CertifiedSlice :=
 ⟨![2,3,2,5], R7.Core.SpectralSliceCertificates.Entry028.polynomial_172, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry028.polynomial_172 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry028.positive_172 y u hy⟩
noncomputable def entrySlice_173 : CertifiedSlice :=
 ⟨![2,3,3,4], R7.Core.SpectralSliceCertificates.Entry028.polynomial_173, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry028.polynomial_173 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry028.positive_173 y u hy⟩
noncomputable def entrySlice_174 : CertifiedSlice :=
 ⟨![2,3,4,3], R7.Core.SpectralSliceCertificates.Entry029.polynomial_174, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry029.polynomial_174 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry029.positive_174 y u hy⟩
noncomputable def entrySlice_175 : CertifiedSlice :=
 ⟨![2,3,5,2], R7.Core.SpectralSliceCertificates.Entry029.polynomial_175, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry029.polynomial_175 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry029.positive_175 y u hy⟩
noncomputable def entrySlice_176 : CertifiedSlice :=
 ⟨![2,4,0,6], R7.Core.SpectralSliceCertificates.Entry029.polynomial_176, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry029.polynomial_176 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry029.positive_176 y u hy⟩
noncomputable def entrySlice_177 : CertifiedSlice :=
 ⟨![2,4,1,5], R7.Core.SpectralSliceCertificates.Entry029.polynomial_177, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry029.polynomial_177 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry029.positive_177 y u hy⟩
noncomputable def entrySlice_178 : CertifiedSlice :=
 ⟨![2,4,2,4], R7.Core.SpectralSliceCertificates.Entry029.polynomial_178, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry029.polynomial_178 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry029.positive_178 y u hy⟩
noncomputable def entrySlice_179 : CertifiedSlice :=
 ⟨![2,4,3,3], R7.Core.SpectralSliceCertificates.Entry029.polynomial_179, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry029.polynomial_179 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry029.positive_179 y u hy⟩
noncomputable def entrySlice_180 : CertifiedSlice :=
 ⟨![2,4,4,2], R7.Core.SpectralSliceCertificates.Entry030.polynomial_180, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry030.polynomial_180 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry030.positive_180 y u hy⟩
noncomputable def entrySlice_181 : CertifiedSlice :=
 ⟨![2,5,0,5], R7.Core.SpectralSliceCertificates.Entry030.polynomial_181, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry030.polynomial_181 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry030.positive_181 y u hy⟩
noncomputable def entrySlice_182 : CertifiedSlice :=
 ⟨![2,5,1,4], R7.Core.SpectralSliceCertificates.Entry030.polynomial_182, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry030.polynomial_182 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry030.positive_182 y u hy⟩
noncomputable def entrySlice_183 : CertifiedSlice :=
 ⟨![2,5,2,3], R7.Core.SpectralSliceCertificates.Entry030.polynomial_183, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry030.polynomial_183 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry030.positive_183 y u hy⟩
noncomputable def entrySlice_184 : CertifiedSlice :=
 ⟨![2,6,0,4], R7.Core.SpectralSliceCertificates.Entry030.polynomial_184, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry030.polynomial_184 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry030.positive_184 y u hy⟩
noncomputable def entrySlice_185 : CertifiedSlice :=
 ⟨![2,6,1,3], R7.Core.SpectralSliceCertificates.Entry030.polynomial_185, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry030.polynomial_185 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry030.positive_185 y u hy⟩
noncomputable def entrySlice_186 : CertifiedSlice :=
 ⟨![2,7,0,3], R7.Core.SpectralSliceCertificates.Entry031.polynomial_186, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry031.polynomial_186 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry031.positive_186 y u hy⟩
noncomputable def entrySlice_187 : CertifiedSlice :=
 ⟨![3,0,0,9], R7.Core.SpectralSliceCertificates.Entry031.polynomial_187, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry031.polynomial_187 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry031.positive_187 y u hy⟩
noncomputable def entrySlice_188 : CertifiedSlice :=
 ⟨![3,0,1,8], R7.Core.SpectralSliceCertificates.Entry031.polynomial_188, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry031.polynomial_188 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry031.positive_188 y u hy⟩
noncomputable def entrySlice_189 : CertifiedSlice :=
 ⟨![3,0,2,7], R7.Core.SpectralSliceCertificates.Entry031.polynomial_189, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry031.polynomial_189 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry031.positive_189 y u hy⟩
noncomputable def entrySlice_190 : CertifiedSlice :=
 ⟨![3,0,3,6], R7.Core.SpectralSliceCertificates.Entry031.polynomial_190, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry031.polynomial_190 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry031.positive_190 y u hy⟩
noncomputable def entrySlice_191 : CertifiedSlice :=
 ⟨![3,0,4,5], R7.Core.SpectralSliceCertificates.Entry031.polynomial_191, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry031.polynomial_191 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry031.positive_191 y u hy⟩
noncomputable def entrySlice_192 : CertifiedSlice :=
 ⟨![3,0,5,4], R7.Core.SpectralSliceCertificates.Entry032.polynomial_192, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry032.polynomial_192 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry032.positive_192 y u hy⟩
noncomputable def entrySlice_193 : CertifiedSlice :=
 ⟨![3,0,6,3], R7.Core.SpectralSliceCertificates.Entry032.polynomial_193, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry032.polynomial_193 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry032.positive_193 y u hy⟩
noncomputable def entrySlice_194 : CertifiedSlice :=
 ⟨![3,1,0,8], R7.Core.SpectralSliceCertificates.Entry032.polynomial_194, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry032.polynomial_194 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry032.positive_194 y u hy⟩
noncomputable def entrySlice_195 : CertifiedSlice :=
 ⟨![3,1,1,7], R7.Core.SpectralSliceCertificates.Entry032.polynomial_195, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry032.polynomial_195 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry032.positive_195 y u hy⟩
noncomputable def entrySlice_196 : CertifiedSlice :=
 ⟨![3,1,2,6], R7.Core.SpectralSliceCertificates.Entry032.polynomial_196, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry032.polynomial_196 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry032.positive_196 y u hy⟩
noncomputable def entrySlice_197 : CertifiedSlice :=
 ⟨![3,1,3,5], R7.Core.SpectralSliceCertificates.Entry032.polynomial_197, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry032.polynomial_197 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry032.positive_197 y u hy⟩
noncomputable def entrySlice_198 : CertifiedSlice :=
 ⟨![3,1,4,4], R7.Core.SpectralSliceCertificates.Entry033.polynomial_198, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry033.polynomial_198 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry033.positive_198 y u hy⟩
noncomputable def entrySlice_199 : CertifiedSlice :=
 ⟨![3,1,5,3], R7.Core.SpectralSliceCertificates.Entry033.polynomial_199, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry033.polynomial_199 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry033.positive_199 y u hy⟩
noncomputable def entrySlice_200 : CertifiedSlice :=
 ⟨![3,2,0,7], R7.Core.SpectralSliceCertificates.Entry033.polynomial_200, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry033.polynomial_200 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry033.positive_200 y u hy⟩
noncomputable def entrySlice_201 : CertifiedSlice :=
 ⟨![3,2,1,6], R7.Core.SpectralSliceCertificates.Entry033.polynomial_201, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry033.polynomial_201 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry033.positive_201 y u hy⟩
noncomputable def entrySlice_202 : CertifiedSlice :=
 ⟨![3,2,2,5], R7.Core.SpectralSliceCertificates.Entry033.polynomial_202, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry033.polynomial_202 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry033.positive_202 y u hy⟩
noncomputable def entrySlice_203 : CertifiedSlice :=
 ⟨![3,2,3,4], R7.Core.SpectralSliceCertificates.Entry033.polynomial_203, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry033.polynomial_203 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry033.positive_203 y u hy⟩
noncomputable def entrySlice_204 : CertifiedSlice :=
 ⟨![3,2,4,3], R7.Core.SpectralSliceCertificates.Entry034.polynomial_204, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry034.polynomial_204 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry034.positive_204 y u hy⟩
noncomputable def entrySlice_205 : CertifiedSlice :=
 ⟨![3,3,0,6], R7.Core.SpectralSliceCertificates.Entry034.polynomial_205, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry034.polynomial_205 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry034.positive_205 y u hy⟩
noncomputable def entrySlice_206 : CertifiedSlice :=
 ⟨![3,3,1,5], R7.Core.SpectralSliceCertificates.Entry034.polynomial_206, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry034.polynomial_206 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry034.positive_206 y u hy⟩
noncomputable def entrySlice_207 : CertifiedSlice :=
 ⟨![3,3,2,4], R7.Core.SpectralSliceCertificates.Entry034.polynomial_207, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry034.polynomial_207 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry034.positive_207 y u hy⟩
noncomputable def entrySlice_208 : CertifiedSlice :=
 ⟨![3,3,3,3], R7.Core.SpectralSliceCertificates.Entry034.polynomial_208, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry034.polynomial_208 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry034.positive_208 y u hy⟩
noncomputable def entrySlice_209 : CertifiedSlice :=
 ⟨![3,4,0,5], R7.Core.SpectralSliceCertificates.Entry034.polynomial_209, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry034.polynomial_209 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry034.positive_209 y u hy⟩
noncomputable def entrySlice_210 : CertifiedSlice :=
 ⟨![3,4,1,4], R7.Core.SpectralSliceCertificates.Entry035.polynomial_210, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry035.polynomial_210 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry035.positive_210 y u hy⟩
noncomputable def entrySlice_211 : CertifiedSlice :=
 ⟨![3,5,0,4], R7.Core.SpectralSliceCertificates.Entry035.polynomial_211, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry035.polynomial_211 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry035.positive_211 y u hy⟩
noncomputable def entrySlice_212 : CertifiedSlice :=
 ⟨![4,0,0,8], R7.Core.SpectralSliceCertificates.Entry035.polynomial_212, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry035.polynomial_212 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry035.positive_212 y u hy⟩
noncomputable def entrySlice_213 : CertifiedSlice :=
 ⟨![4,0,1,7], R7.Core.SpectralSliceCertificates.Entry035.polynomial_213, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry035.polynomial_213 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry035.positive_213 y u hy⟩
noncomputable def entrySlice_214 : CertifiedSlice :=
 ⟨![4,0,2,6], R7.Core.SpectralSliceCertificates.Entry035.polynomial_214, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry035.polynomial_214 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry035.positive_214 y u hy⟩
noncomputable def entrySlice_215 : CertifiedSlice :=
 ⟨![4,0,3,5], R7.Core.SpectralSliceCertificates.Entry035.polynomial_215, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry035.polynomial_215 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry035.positive_215 y u hy⟩
noncomputable def entrySlice_216 : CertifiedSlice :=
 ⟨![4,0,4,4], R7.Core.SpectralSliceCertificates.Entry036.polynomial_216, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry036.polynomial_216 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry036.positive_216 y u hy⟩
noncomputable def entrySlice_217 : CertifiedSlice :=
 ⟨![4,1,0,7], R7.Core.SpectralSliceCertificates.Entry036.polynomial_217, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry036.polynomial_217 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry036.positive_217 y u hy⟩
noncomputable def entrySlice_218 : CertifiedSlice :=
 ⟨![4,1,1,6], R7.Core.SpectralSliceCertificates.Entry036.polynomial_218, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry036.polynomial_218 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry036.positive_218 y u hy⟩
noncomputable def entrySlice_219 : CertifiedSlice :=
 ⟨![4,1,2,5], R7.Core.SpectralSliceCertificates.Entry036.polynomial_219, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry036.polynomial_219 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry036.positive_219 y u hy⟩
noncomputable def entrySlice_220 : CertifiedSlice :=
 ⟨![4,1,3,4], R7.Core.SpectralSliceCertificates.Entry036.polynomial_220, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry036.polynomial_220 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry036.positive_220 y u hy⟩
noncomputable def entrySlice_221 : CertifiedSlice :=
 ⟨![4,2,0,6], R7.Core.SpectralSliceCertificates.Entry036.polynomial_221, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry036.polynomial_221 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry036.positive_221 y u hy⟩
noncomputable def entrySlice_222 : CertifiedSlice :=
 ⟨![4,2,1,5], R7.Core.SpectralSliceCertificates.Entry037.polynomial_222, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry037.polynomial_222 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry037.positive_222 y u hy⟩
noncomputable def entrySlice_223 : CertifiedSlice :=
 ⟨![4,2,2,4], R7.Core.SpectralSliceCertificates.Entry037.polynomial_223, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry037.polynomial_223 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry037.positive_223 y u hy⟩
noncomputable def entrySlice_224 : CertifiedSlice :=
 ⟨![4,3,0,5], R7.Core.SpectralSliceCertificates.Entry037.polynomial_224, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry037.polynomial_224 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry037.positive_224 y u hy⟩
noncomputable def entrySlice_225 : CertifiedSlice :=
 ⟨![5,0,0,7], R7.Core.SpectralSliceCertificates.Entry037.polynomial_225, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry037.polynomial_225 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry037.positive_225 y u hy⟩
noncomputable def entrySlice_226 : CertifiedSlice :=
 ⟨![5,0,1,6], R7.Core.SpectralSliceCertificates.Entry037.polynomial_226, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry037.polynomial_226 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry037.positive_226 y u hy⟩
noncomputable def entrySlice_227 : CertifiedSlice :=
 ⟨![5,0,2,5], R7.Core.SpectralSliceCertificates.Entry037.polynomial_227, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry037.polynomial_227 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry037.positive_227 y u hy⟩
noncomputable def entrySlice_228 : CertifiedSlice :=
 ⟨![5,1,0,6], R7.Core.SpectralSliceCertificates.Entry038.polynomial_228, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry038.polynomial_228 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry038.positive_228 y u hy⟩
noncomputable def entrySlice_229 : CertifiedSlice :=
 ⟨![5,1,1,5], R7.Core.SpectralSliceCertificates.Entry038.polynomial_229, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry038.polynomial_229 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry038.positive_229 y u hy⟩
noncomputable def entrySlice_230 : CertifiedSlice :=
 ⟨![6,0,0,6], R7.Core.SpectralSliceCertificates.Entry038.polynomial_230, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.Entry038.polynomial_230 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.Entry038.positive_230 y u hy⟩
noncomputable def entryCertified : List CertifiedSlice := [
 entrySlice_0,
 entrySlice_1,
 entrySlice_2,
 entrySlice_3,
 entrySlice_4,
 entrySlice_5,
 entrySlice_6,
 entrySlice_7,
 entrySlice_8,
 entrySlice_9,
 entrySlice_10,
 entrySlice_11,
 entrySlice_12,
 entrySlice_13,
 entrySlice_14,
 entrySlice_15,
 entrySlice_16,
 entrySlice_17,
 entrySlice_18,
 entrySlice_19,
 entrySlice_20,
 entrySlice_21,
 entrySlice_22,
 entrySlice_23,
 entrySlice_24,
 entrySlice_25,
 entrySlice_26,
 entrySlice_27,
 entrySlice_28,
 entrySlice_29,
 entrySlice_30,
 entrySlice_31,
 entrySlice_32,
 entrySlice_33,
 entrySlice_34,
 entrySlice_35,
 entrySlice_36,
 entrySlice_37,
 entrySlice_38,
 entrySlice_39,
 entrySlice_40,
 entrySlice_41,
 entrySlice_42,
 entrySlice_43,
 entrySlice_44,
 entrySlice_45,
 entrySlice_46,
 entrySlice_47,
 entrySlice_48,
 entrySlice_49,
 entrySlice_50,
 entrySlice_51,
 entrySlice_52,
 entrySlice_53,
 entrySlice_54,
 entrySlice_55,
 entrySlice_56,
 entrySlice_57,
 entrySlice_58,
 entrySlice_59,
 entrySlice_60,
 entrySlice_61,
 entrySlice_62,
 entrySlice_63,
 entrySlice_64,
 entrySlice_65,
 entrySlice_66,
 entrySlice_67,
 entrySlice_68,
 entrySlice_69,
 entrySlice_70,
 entrySlice_71,
 entrySlice_72,
 entrySlice_73,
 entrySlice_74,
 CertifiedSlice.reflected ![0,7,5,0] (entrySlice_62),
 entrySlice_75,
 entrySlice_76,
 entrySlice_77,
 entrySlice_78,
 CertifiedSlice.reflected ![0,8,4,0] (entrySlice_54),
 entrySlice_79,
 entrySlice_80,
 entrySlice_81,
 CertifiedSlice.reflected ![0,9,3,0] (entrySlice_45),
 entrySlice_82,
 entrySlice_83,
 CertifiedSlice.reflected ![0,10,2,0] (entrySlice_35),
 entrySlice_84,
 CertifiedSlice.reflected ![0,11,1,0] (entrySlice_24),
 CertifiedSlice.reflected ![0,12,0,0] (entrySlice_12),
 entrySlice_85,
 entrySlice_86,
 entrySlice_87,
 entrySlice_88,
 entrySlice_89,
 entrySlice_90,
 entrySlice_91,
 entrySlice_92,
 entrySlice_93,
 entrySlice_94,
 entrySlice_95,
 CertifiedSlice.reflected ![1,0,11,0] (entrySlice_84),
 entrySlice_96,
 entrySlice_97,
 entrySlice_98,
 entrySlice_99,
 entrySlice_100,
 entrySlice_101,
 entrySlice_102,
 entrySlice_103,
 entrySlice_104,
 entrySlice_105,
 CertifiedSlice.reflected ![1,1,10,0] (entrySlice_83),
 entrySlice_106,
 entrySlice_107,
 entrySlice_108,
 entrySlice_109,
 entrySlice_110,
 entrySlice_111,
 entrySlice_112,
 entrySlice_113,
 entrySlice_114,
 CertifiedSlice.reflected ![1,2,9,0] (entrySlice_81),
 entrySlice_115,
 entrySlice_116,
 entrySlice_117,
 entrySlice_118,
 entrySlice_119,
 entrySlice_120,
 entrySlice_121,
 entrySlice_122,
 CertifiedSlice.reflected ![1,3,8,0] (entrySlice_78),
 entrySlice_123,
 entrySlice_124,
 entrySlice_125,
 entrySlice_126,
 entrySlice_127,
 entrySlice_128,
 entrySlice_129,
 CertifiedSlice.reflected ![1,4,7,0] (entrySlice_74),
 entrySlice_130,
 entrySlice_131,
 entrySlice_132,
 entrySlice_133,
 entrySlice_134,
 entrySlice_135,
 CertifiedSlice.reflected ![1,5,6,0] (entrySlice_68),
 entrySlice_136,
 entrySlice_137,
 entrySlice_138,
 entrySlice_139,
 CertifiedSlice.reflected ![1,6,4,1] (entrySlice_129),
 CertifiedSlice.reflected ![1,6,5,0] (entrySlice_61),
 entrySlice_140,
 entrySlice_141,
 entrySlice_142,
 CertifiedSlice.reflected ![1,7,3,1] (entrySlice_122),
 CertifiedSlice.reflected ![1,7,4,0] (entrySlice_53),
 entrySlice_143,
 entrySlice_144,
 CertifiedSlice.reflected ![1,8,2,1] (entrySlice_114),
 CertifiedSlice.reflected ![1,8,3,0] (entrySlice_44),
 entrySlice_145,
 CertifiedSlice.reflected ![1,9,1,1] (entrySlice_105),
 CertifiedSlice.reflected ![1,9,2,0] (entrySlice_34),
 CertifiedSlice.reflected ![1,10,0,1] (entrySlice_95),
 CertifiedSlice.reflected ![1,10,1,0] (entrySlice_23),
 CertifiedSlice.reflected ![1,11,0,0] (entrySlice_11),
 entrySlice_146,
 entrySlice_147,
 entrySlice_148,
 entrySlice_149,
 entrySlice_150,
 entrySlice_151,
 entrySlice_152,
 entrySlice_153,
 entrySlice_154,
 CertifiedSlice.reflected ![2,0,9,1] (entrySlice_145),
 CertifiedSlice.reflected ![2,0,10,0] (entrySlice_82),
 entrySlice_155,
 entrySlice_156,
 entrySlice_157,
 entrySlice_158,
 entrySlice_159,
 entrySlice_160,
 entrySlice_161,
 entrySlice_162,
 CertifiedSlice.reflected ![2,1,8,1] (entrySlice_144),
 CertifiedSlice.reflected ![2,1,9,0] (entrySlice_80),
 entrySlice_163,
 entrySlice_164,
 entrySlice_165,
 entrySlice_166,
 entrySlice_167,
 entrySlice_168,
 entrySlice_169,
 CertifiedSlice.reflected ![2,2,7,1] (entrySlice_142),
 CertifiedSlice.reflected ![2,2,8,0] (entrySlice_77),
 entrySlice_170,
 entrySlice_171,
 entrySlice_172,
 entrySlice_173,
 entrySlice_174,
 entrySlice_175,
 CertifiedSlice.reflected ![2,3,6,1] (entrySlice_139),
 CertifiedSlice.reflected ![2,3,7,0] (entrySlice_73),
 entrySlice_176,
 entrySlice_177,
 entrySlice_178,
 entrySlice_179,
 entrySlice_180,
 CertifiedSlice.reflected ![2,4,5,1] (entrySlice_134),
 CertifiedSlice.reflected ![2,4,6,0] (entrySlice_67),
 entrySlice_181,
 entrySlice_182,
 entrySlice_183,
 CertifiedSlice.reflected ![2,5,3,2] (entrySlice_175),
 CertifiedSlice.reflected ![2,5,4,1] (entrySlice_128),
 CertifiedSlice.reflected ![2,5,5,0] (entrySlice_60),
 entrySlice_184,
 entrySlice_185,
 CertifiedSlice.reflected ![2,6,2,2] (entrySlice_169),
 CertifiedSlice.reflected ![2,6,3,1] (entrySlice_121),
 CertifiedSlice.reflected ![2,6,4,0] (entrySlice_52),
 entrySlice_186,
 CertifiedSlice.reflected ![2,7,1,2] (entrySlice_162),
 CertifiedSlice.reflected ![2,7,2,1] (entrySlice_113),
 CertifiedSlice.reflected ![2,7,3,0] (entrySlice_43),
 CertifiedSlice.reflected ![2,8,0,2] (entrySlice_154),
 CertifiedSlice.reflected ![2,8,1,1] (entrySlice_104),
 CertifiedSlice.reflected ![2,8,2,0] (entrySlice_33),
 CertifiedSlice.reflected ![2,9,0,1] (entrySlice_94),
 CertifiedSlice.reflected ![2,9,1,0] (entrySlice_22),
 CertifiedSlice.reflected ![2,10,0,0] (entrySlice_10),
 entrySlice_187,
 entrySlice_188,
 entrySlice_189,
 entrySlice_190,
 entrySlice_191,
 entrySlice_192,
 entrySlice_193,
 CertifiedSlice.reflected ![3,0,7,2] (entrySlice_186),
 CertifiedSlice.reflected ![3,0,8,1] (entrySlice_143),
 CertifiedSlice.reflected ![3,0,9,0] (entrySlice_79),
 entrySlice_194,
 entrySlice_195,
 entrySlice_196,
 entrySlice_197,
 entrySlice_198,
 entrySlice_199,
 CertifiedSlice.reflected ![3,1,6,2] (entrySlice_185),
 CertifiedSlice.reflected ![3,1,7,1] (entrySlice_141),
 CertifiedSlice.reflected ![3,1,8,0] (entrySlice_76),
 entrySlice_200,
 entrySlice_201,
 entrySlice_202,
 entrySlice_203,
 entrySlice_204,
 CertifiedSlice.reflected ![3,2,5,2] (entrySlice_183),
 CertifiedSlice.reflected ![3,2,6,1] (entrySlice_138),
 CertifiedSlice.reflected ![3,2,7,0] (entrySlice_72),
 entrySlice_205,
 entrySlice_206,
 entrySlice_207,
 entrySlice_208,
 CertifiedSlice.reflected ![3,3,4,2] (entrySlice_179),
 CertifiedSlice.reflected ![3,3,5,1] (entrySlice_133),
 CertifiedSlice.reflected ![3,3,6,0] (entrySlice_66),
 entrySlice_209,
 entrySlice_210,
 CertifiedSlice.reflected ![3,4,2,3] (entrySlice_204),
 CertifiedSlice.reflected ![3,4,3,2] (entrySlice_174),
 CertifiedSlice.reflected ![3,4,4,1] (entrySlice_127),
 CertifiedSlice.reflected ![3,4,5,0] (entrySlice_59),
 entrySlice_211,
 CertifiedSlice.reflected ![3,5,1,3] (entrySlice_199),
 CertifiedSlice.reflected ![3,5,2,2] (entrySlice_168),
 CertifiedSlice.reflected ![3,5,3,1] (entrySlice_120),
 CertifiedSlice.reflected ![3,5,4,0] (entrySlice_51),
 CertifiedSlice.reflected ![3,6,0,3] (entrySlice_193),
 CertifiedSlice.reflected ![3,6,1,2] (entrySlice_161),
 CertifiedSlice.reflected ![3,6,2,1] (entrySlice_112),
 CertifiedSlice.reflected ![3,6,3,0] (entrySlice_42),
 CertifiedSlice.reflected ![3,7,0,2] (entrySlice_153),
 CertifiedSlice.reflected ![3,7,1,1] (entrySlice_103),
 CertifiedSlice.reflected ![3,7,2,0] (entrySlice_32),
 CertifiedSlice.reflected ![3,8,0,1] (entrySlice_93),
 CertifiedSlice.reflected ![3,8,1,0] (entrySlice_21),
 CertifiedSlice.reflected ![3,9,0,0] (entrySlice_9),
 entrySlice_212,
 entrySlice_213,
 entrySlice_214,
 entrySlice_215,
 entrySlice_216,
 CertifiedSlice.reflected ![4,0,5,3] (entrySlice_211),
 CertifiedSlice.reflected ![4,0,6,2] (entrySlice_184),
 CertifiedSlice.reflected ![4,0,7,1] (entrySlice_140),
 CertifiedSlice.reflected ![4,0,8,0] (entrySlice_75),
 entrySlice_217,
 entrySlice_218,
 entrySlice_219,
 entrySlice_220,
 CertifiedSlice.reflected ![4,1,4,3] (entrySlice_210),
 CertifiedSlice.reflected ![4,1,5,2] (entrySlice_182),
 CertifiedSlice.reflected ![4,1,6,1] (entrySlice_137),
 CertifiedSlice.reflected ![4,1,7,0] (entrySlice_71),
 entrySlice_221,
 entrySlice_222,
 entrySlice_223,
 CertifiedSlice.reflected ![4,2,3,3] (entrySlice_207),
 CertifiedSlice.reflected ![4,2,4,2] (entrySlice_178),
 CertifiedSlice.reflected ![4,2,5,1] (entrySlice_132),
 CertifiedSlice.reflected ![4,2,6,0] (entrySlice_65),
 entrySlice_224,
 CertifiedSlice.reflected ![4,3,1,4] (entrySlice_220),
 CertifiedSlice.reflected ![4,3,2,3] (entrySlice_203),
 CertifiedSlice.reflected ![4,3,3,2] (entrySlice_173),
 CertifiedSlice.reflected ![4,3,4,1] (entrySlice_126),
 CertifiedSlice.reflected ![4,3,5,0] (entrySlice_58),
 CertifiedSlice.reflected ![4,4,0,4] (entrySlice_216),
 CertifiedSlice.reflected ![4,4,1,3] (entrySlice_198),
 CertifiedSlice.reflected ![4,4,2,2] (entrySlice_167),
 CertifiedSlice.reflected ![4,4,3,1] (entrySlice_119),
 CertifiedSlice.reflected ![4,4,4,0] (entrySlice_50),
 CertifiedSlice.reflected ![4,5,0,3] (entrySlice_192),
 CertifiedSlice.reflected ![4,5,1,2] (entrySlice_160),
 CertifiedSlice.reflected ![4,5,2,1] (entrySlice_111),
 CertifiedSlice.reflected ![4,5,3,0] (entrySlice_41),
 CertifiedSlice.reflected ![4,6,0,2] (entrySlice_152),
 CertifiedSlice.reflected ![4,6,1,1] (entrySlice_102),
 CertifiedSlice.reflected ![4,6,2,0] (entrySlice_31),
 CertifiedSlice.reflected ![4,7,0,1] (entrySlice_92),
 CertifiedSlice.reflected ![4,7,1,0] (entrySlice_20),
 CertifiedSlice.reflected ![4,8,0,0] (entrySlice_8),
 entrySlice_225,
 entrySlice_226,
 entrySlice_227,
 CertifiedSlice.reflected ![5,0,3,4] (entrySlice_224),
 CertifiedSlice.reflected ![5,0,4,3] (entrySlice_209),
 CertifiedSlice.reflected ![5,0,5,2] (entrySlice_181),
 CertifiedSlice.reflected ![5,0,6,1] (entrySlice_136),
 CertifiedSlice.reflected ![5,0,7,0] (entrySlice_70),
 entrySlice_228,
 entrySlice_229,
 CertifiedSlice.reflected ![5,1,2,4] (entrySlice_222),
 CertifiedSlice.reflected ![5,1,3,3] (entrySlice_206),
 CertifiedSlice.reflected ![5,1,4,2] (entrySlice_177),
 CertifiedSlice.reflected ![5,1,5,1] (entrySlice_131),
 CertifiedSlice.reflected ![5,1,6,0] (entrySlice_64),
 CertifiedSlice.reflected ![5,2,0,5] (entrySlice_227),
 CertifiedSlice.reflected ![5,2,1,4] (entrySlice_219),
 CertifiedSlice.reflected ![5,2,2,3] (entrySlice_202),
 CertifiedSlice.reflected ![5,2,3,2] (entrySlice_172),
 CertifiedSlice.reflected ![5,2,4,1] (entrySlice_125),
 CertifiedSlice.reflected ![5,2,5,0] (entrySlice_57),
 CertifiedSlice.reflected ![5,3,0,4] (entrySlice_215),
 CertifiedSlice.reflected ![5,3,1,3] (entrySlice_197),
 CertifiedSlice.reflected ![5,3,2,2] (entrySlice_166),
 CertifiedSlice.reflected ![5,3,3,1] (entrySlice_118),
 CertifiedSlice.reflected ![5,3,4,0] (entrySlice_49),
 CertifiedSlice.reflected ![5,4,0,3] (entrySlice_191),
 CertifiedSlice.reflected ![5,4,1,2] (entrySlice_159),
 CertifiedSlice.reflected ![5,4,2,1] (entrySlice_110),
 CertifiedSlice.reflected ![5,4,3,0] (entrySlice_40),
 CertifiedSlice.reflected ![5,5,0,2] (entrySlice_151),
 CertifiedSlice.reflected ![5,5,1,1] (entrySlice_101),
 CertifiedSlice.reflected ![5,5,2,0] (entrySlice_30),
 CertifiedSlice.reflected ![5,6,0,1] (entrySlice_91),
 CertifiedSlice.reflected ![5,6,1,0] (entrySlice_19),
 CertifiedSlice.reflected ![5,7,0,0] (entrySlice_7),
 entrySlice_230,
 CertifiedSlice.reflected ![6,0,1,5] (entrySlice_228),
 CertifiedSlice.reflected ![6,0,2,4] (entrySlice_221),
 CertifiedSlice.reflected ![6,0,3,3] (entrySlice_205),
 CertifiedSlice.reflected ![6,0,4,2] (entrySlice_176),
 CertifiedSlice.reflected ![6,0,5,1] (entrySlice_130),
 CertifiedSlice.reflected ![6,0,6,0] (entrySlice_63),
 CertifiedSlice.reflected ![6,1,0,5] (entrySlice_226),
 CertifiedSlice.reflected ![6,1,1,4] (entrySlice_218),
 CertifiedSlice.reflected ![6,1,2,3] (entrySlice_201),
 CertifiedSlice.reflected ![6,1,3,2] (entrySlice_171),
 CertifiedSlice.reflected ![6,1,4,1] (entrySlice_124),
 CertifiedSlice.reflected ![6,1,5,0] (entrySlice_56),
 CertifiedSlice.reflected ![6,2,0,4] (entrySlice_214),
 CertifiedSlice.reflected ![6,2,1,3] (entrySlice_196),
 CertifiedSlice.reflected ![6,2,2,2] (entrySlice_165),
 CertifiedSlice.reflected ![6,2,3,1] (entrySlice_117),
 CertifiedSlice.reflected ![6,2,4,0] (entrySlice_48),
 CertifiedSlice.reflected ![6,3,0,3] (entrySlice_190),
 CertifiedSlice.reflected ![6,3,1,2] (entrySlice_158),
 CertifiedSlice.reflected ![6,3,2,1] (entrySlice_109),
 CertifiedSlice.reflected ![6,3,3,0] (entrySlice_39),
 CertifiedSlice.reflected ![6,4,0,2] (entrySlice_150),
 CertifiedSlice.reflected ![6,4,1,1] (entrySlice_100),
 CertifiedSlice.reflected ![6,4,2,0] (entrySlice_29),
 CertifiedSlice.reflected ![6,5,0,1] (entrySlice_90),
 CertifiedSlice.reflected ![6,5,1,0] (entrySlice_18),
 CertifiedSlice.reflected ![6,6,0,0] (entrySlice_6),
 CertifiedSlice.reflected ![7,0,0,5] (entrySlice_225),
 CertifiedSlice.reflected ![7,0,1,4] (entrySlice_217),
 CertifiedSlice.reflected ![7,0,2,3] (entrySlice_200),
 CertifiedSlice.reflected ![7,0,3,2] (entrySlice_170),
 CertifiedSlice.reflected ![7,0,4,1] (entrySlice_123),
 CertifiedSlice.reflected ![7,0,5,0] (entrySlice_55),
 CertifiedSlice.reflected ![7,1,0,4] (entrySlice_213),
 CertifiedSlice.reflected ![7,1,1,3] (entrySlice_195),
 CertifiedSlice.reflected ![7,1,2,2] (entrySlice_164),
 CertifiedSlice.reflected ![7,1,3,1] (entrySlice_116),
 CertifiedSlice.reflected ![7,1,4,0] (entrySlice_47),
 CertifiedSlice.reflected ![7,2,0,3] (entrySlice_189),
 CertifiedSlice.reflected ![7,2,1,2] (entrySlice_157),
 CertifiedSlice.reflected ![7,2,2,1] (entrySlice_108),
 CertifiedSlice.reflected ![7,2,3,0] (entrySlice_38),
 CertifiedSlice.reflected ![7,3,0,2] (entrySlice_149),
 CertifiedSlice.reflected ![7,3,1,1] (entrySlice_99),
 CertifiedSlice.reflected ![7,3,2,0] (entrySlice_28),
 CertifiedSlice.reflected ![7,4,0,1] (entrySlice_89),
 CertifiedSlice.reflected ![7,4,1,0] (entrySlice_17),
 CertifiedSlice.reflected ![7,5,0,0] (entrySlice_5),
 CertifiedSlice.reflected ![8,0,0,4] (entrySlice_212),
 CertifiedSlice.reflected ![8,0,1,3] (entrySlice_194),
 CertifiedSlice.reflected ![8,0,2,2] (entrySlice_163),
 CertifiedSlice.reflected ![8,0,3,1] (entrySlice_115),
 CertifiedSlice.reflected ![8,0,4,0] (entrySlice_46),
 CertifiedSlice.reflected ![8,1,0,3] (entrySlice_188),
 CertifiedSlice.reflected ![8,1,1,2] (entrySlice_156),
 CertifiedSlice.reflected ![8,1,2,1] (entrySlice_107),
 CertifiedSlice.reflected ![8,1,3,0] (entrySlice_37),
 CertifiedSlice.reflected ![8,2,0,2] (entrySlice_148),
 CertifiedSlice.reflected ![8,2,1,1] (entrySlice_98),
 CertifiedSlice.reflected ![8,2,2,0] (entrySlice_27),
 CertifiedSlice.reflected ![8,3,0,1] (entrySlice_88),
 CertifiedSlice.reflected ![8,3,1,0] (entrySlice_16),
 CertifiedSlice.reflected ![8,4,0,0] (entrySlice_4),
 CertifiedSlice.reflected ![9,0,0,3] (entrySlice_187),
 CertifiedSlice.reflected ![9,0,1,2] (entrySlice_155),
 CertifiedSlice.reflected ![9,0,2,1] (entrySlice_106),
 CertifiedSlice.reflected ![9,0,3,0] (entrySlice_36),
 CertifiedSlice.reflected ![9,1,0,2] (entrySlice_147),
 CertifiedSlice.reflected ![9,1,1,1] (entrySlice_97),
 CertifiedSlice.reflected ![9,1,2,0] (entrySlice_26),
 CertifiedSlice.reflected ![9,2,0,1] (entrySlice_87),
 CertifiedSlice.reflected ![9,2,1,0] (entrySlice_15),
 CertifiedSlice.reflected ![9,3,0,0] (entrySlice_3),
 CertifiedSlice.reflected ![10,0,0,2] (entrySlice_146),
 CertifiedSlice.reflected ![10,0,1,1] (entrySlice_96),
 CertifiedSlice.reflected ![10,0,2,0] (entrySlice_25),
 CertifiedSlice.reflected ![10,1,0,1] (entrySlice_86),
 CertifiedSlice.reflected ![10,1,1,0] (entrySlice_14),
 CertifiedSlice.reflected ![10,2,0,0] (entrySlice_2),
 CertifiedSlice.reflected ![11,0,0,1] (entrySlice_85),
 CertifiedSlice.reflected ![11,0,1,0] (entrySlice_13),
 CertifiedSlice.reflected ![11,1,0,0] (entrySlice_1),
 CertifiedSlice.reflected ![12,0,0,0] (entrySlice_0)
]
noncomputable def entryGroups : Groups := entryCertified.map CertifiedSlice.row
theorem entryGroups_positive (row) (hrow : row ∈ entryGroups) (u y : ℝ) (hy : 0 ≤ y) :
 0 < eval row.2 u y := certifiedRows_positive entryCertified row hrow u y hy
theorem entryGroups_short : ∀ row ∈ entryGroups, ∀ a ∈ row.2, a.length ≤ 3 := by
 decide +kernel
noncomputable def criticalLSlice_0 : CertifiedSlice :=
 ⟨![0,0,0,12], R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_0, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_0 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL000.positive_0 y u hy⟩
noncomputable def criticalLSlice_1 : CertifiedSlice :=
 ⟨![0,0,1,11], R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_1, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_1 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL000.positive_1 y u hy⟩
noncomputable def criticalLSlice_2 : CertifiedSlice :=
 ⟨![0,0,2,10], R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_2, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_2 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL000.positive_2 y u hy⟩
noncomputable def criticalLSlice_3 : CertifiedSlice :=
 ⟨![0,0,3,9], R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_3, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_3 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL000.positive_3 y u hy⟩
noncomputable def criticalLSlice_4 : CertifiedSlice :=
 ⟨![0,0,4,8], R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_4, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_4 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL000.positive_4 y u hy⟩
noncomputable def criticalLSlice_5 : CertifiedSlice :=
 ⟨![0,0,5,7], R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_5, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL000.polynomial_5 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL000.positive_5 y u hy⟩
noncomputable def criticalLSlice_6 : CertifiedSlice :=
 ⟨![0,0,6,6], R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_6, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_6 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL001.positive_6 y u hy⟩
noncomputable def criticalLSlice_7 : CertifiedSlice :=
 ⟨![0,0,7,5], R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_7, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_7 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL001.positive_7 y u hy⟩
noncomputable def criticalLSlice_8 : CertifiedSlice :=
 ⟨![0,0,8,4], R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_8, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_8 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL001.positive_8 y u hy⟩
noncomputable def criticalLSlice_9 : CertifiedSlice :=
 ⟨![0,0,9,3], R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_9, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_9 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL001.positive_9 y u hy⟩
noncomputable def criticalLSlice_10 : CertifiedSlice :=
 ⟨![0,0,10,2], R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_10, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_10 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL001.positive_10 y u hy⟩
noncomputable def criticalLSlice_11 : CertifiedSlice :=
 ⟨![0,0,11,1], R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_11, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL001.polynomial_11 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL001.positive_11 y u hy⟩
noncomputable def criticalLSlice_12 : CertifiedSlice :=
 ⟨![0,0,12,0], R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_12, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_12 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL002.positive_12 y u hy⟩
noncomputable def criticalLSlice_13 : CertifiedSlice :=
 ⟨![0,1,0,11], R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_13, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_13 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL002.positive_13 y u hy⟩
noncomputable def criticalLSlice_14 : CertifiedSlice :=
 ⟨![0,1,1,10], R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_14, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_14 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL002.positive_14 y u hy⟩
noncomputable def criticalLSlice_15 : CertifiedSlice :=
 ⟨![0,1,2,9], R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_15, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_15 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL002.positive_15 y u hy⟩
noncomputable def criticalLSlice_16 : CertifiedSlice :=
 ⟨![0,1,3,8], R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_16, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_16 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL002.positive_16 y u hy⟩
noncomputable def criticalLSlice_17 : CertifiedSlice :=
 ⟨![0,1,4,7], R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_17, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL002.polynomial_17 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL002.positive_17 y u hy⟩
noncomputable def criticalLSlice_18 : CertifiedSlice :=
 ⟨![0,1,5,6], R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_18, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_18 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL003.positive_18 y u hy⟩
noncomputable def criticalLSlice_19 : CertifiedSlice :=
 ⟨![0,1,6,5], R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_19, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_19 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL003.positive_19 y u hy⟩
noncomputable def criticalLSlice_20 : CertifiedSlice :=
 ⟨![0,1,7,4], R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_20, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_20 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL003.positive_20 y u hy⟩
noncomputable def criticalLSlice_21 : CertifiedSlice :=
 ⟨![0,1,8,3], R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_21, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_21 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL003.positive_21 y u hy⟩
noncomputable def criticalLSlice_22 : CertifiedSlice :=
 ⟨![0,1,9,2], R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_22, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_22 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL003.positive_22 y u hy⟩
noncomputable def criticalLSlice_23 : CertifiedSlice :=
 ⟨![0,1,10,1], R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_23, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL003.polynomial_23 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL003.positive_23 y u hy⟩
noncomputable def criticalLSlice_24 : CertifiedSlice :=
 ⟨![0,1,11,0], R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_24, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_24 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL004.positive_24 y u hy⟩
noncomputable def criticalLSlice_25 : CertifiedSlice :=
 ⟨![0,2,0,10], R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_25, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_25 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL004.positive_25 y u hy⟩
noncomputable def criticalLSlice_26 : CertifiedSlice :=
 ⟨![0,2,1,9], R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_26, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_26 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL004.positive_26 y u hy⟩
noncomputable def criticalLSlice_27 : CertifiedSlice :=
 ⟨![0,2,2,8], R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_27, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_27 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL004.positive_27 y u hy⟩
noncomputable def criticalLSlice_28 : CertifiedSlice :=
 ⟨![0,2,3,7], R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_28, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_28 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL004.positive_28 y u hy⟩
noncomputable def criticalLSlice_29 : CertifiedSlice :=
 ⟨![0,2,4,6], R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_29, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL004.polynomial_29 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL004.positive_29 y u hy⟩
noncomputable def criticalLSlice_30 : CertifiedSlice :=
 ⟨![0,2,5,5], R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_30, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_30 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL005.positive_30 y u hy⟩
noncomputable def criticalLSlice_31 : CertifiedSlice :=
 ⟨![0,2,6,4], R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_31, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_31 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL005.positive_31 y u hy⟩
noncomputable def criticalLSlice_32 : CertifiedSlice :=
 ⟨![0,2,7,3], R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_32, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_32 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL005.positive_32 y u hy⟩
noncomputable def criticalLSlice_33 : CertifiedSlice :=
 ⟨![0,2,8,2], R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_33, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_33 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL005.positive_33 y u hy⟩
noncomputable def criticalLSlice_34 : CertifiedSlice :=
 ⟨![0,2,9,1], R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_34, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_34 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL005.positive_34 y u hy⟩
noncomputable def criticalLSlice_35 : CertifiedSlice :=
 ⟨![0,2,10,0], R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_35, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL005.polynomial_35 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL005.positive_35 y u hy⟩
noncomputable def criticalLSlice_36 : CertifiedSlice :=
 ⟨![0,3,0,9], R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_36, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_36 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL006.positive_36 y u hy⟩
noncomputable def criticalLSlice_37 : CertifiedSlice :=
 ⟨![0,3,1,8], R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_37, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_37 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL006.positive_37 y u hy⟩
noncomputable def criticalLSlice_38 : CertifiedSlice :=
 ⟨![0,3,2,7], R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_38, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_38 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL006.positive_38 y u hy⟩
noncomputable def criticalLSlice_39 : CertifiedSlice :=
 ⟨![0,3,3,6], R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_39, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_39 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL006.positive_39 y u hy⟩
noncomputable def criticalLSlice_40 : CertifiedSlice :=
 ⟨![0,3,4,5], R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_40, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_40 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL006.positive_40 y u hy⟩
noncomputable def criticalLSlice_41 : CertifiedSlice :=
 ⟨![0,3,5,4], R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_41, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL006.polynomial_41 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL006.positive_41 y u hy⟩
noncomputable def criticalLSlice_42 : CertifiedSlice :=
 ⟨![0,3,6,3], R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_42, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_42 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL007.positive_42 y u hy⟩
noncomputable def criticalLSlice_43 : CertifiedSlice :=
 ⟨![0,3,7,2], R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_43, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_43 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL007.positive_43 y u hy⟩
noncomputable def criticalLSlice_44 : CertifiedSlice :=
 ⟨![0,3,8,1], R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_44, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_44 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL007.positive_44 y u hy⟩
noncomputable def criticalLSlice_45 : CertifiedSlice :=
 ⟨![0,3,9,0], R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_45, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_45 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL007.positive_45 y u hy⟩
noncomputable def criticalLSlice_46 : CertifiedSlice :=
 ⟨![0,4,0,8], R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_46, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_46 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL007.positive_46 y u hy⟩
noncomputable def criticalLSlice_47 : CertifiedSlice :=
 ⟨![0,4,1,7], R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_47, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL007.polynomial_47 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL007.positive_47 y u hy⟩
noncomputable def criticalLSlice_48 : CertifiedSlice :=
 ⟨![0,4,2,6], R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_48, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_48 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL008.positive_48 y u hy⟩
noncomputable def criticalLSlice_49 : CertifiedSlice :=
 ⟨![0,4,3,5], R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_49, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_49 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL008.positive_49 y u hy⟩
noncomputable def criticalLSlice_50 : CertifiedSlice :=
 ⟨![0,4,4,4], R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_50, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_50 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL008.positive_50 y u hy⟩
noncomputable def criticalLSlice_51 : CertifiedSlice :=
 ⟨![0,4,5,3], R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_51, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_51 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL008.positive_51 y u hy⟩
noncomputable def criticalLSlice_52 : CertifiedSlice :=
 ⟨![0,4,6,2], R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_52, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_52 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL008.positive_52 y u hy⟩
noncomputable def criticalLSlice_53 : CertifiedSlice :=
 ⟨![0,4,7,1], R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_53, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL008.polynomial_53 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL008.positive_53 y u hy⟩
noncomputable def criticalLSlice_54 : CertifiedSlice :=
 ⟨![0,4,8,0], R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_54, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_54 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL009.positive_54 y u hy⟩
noncomputable def criticalLSlice_55 : CertifiedSlice :=
 ⟨![0,5,0,7], R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_55, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_55 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL009.positive_55 y u hy⟩
noncomputable def criticalLSlice_56 : CertifiedSlice :=
 ⟨![0,5,1,6], R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_56, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_56 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL009.positive_56 y u hy⟩
noncomputable def criticalLSlice_57 : CertifiedSlice :=
 ⟨![0,5,2,5], R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_57, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_57 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL009.positive_57 y u hy⟩
noncomputable def criticalLSlice_58 : CertifiedSlice :=
 ⟨![0,5,3,4], R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_58, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_58 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL009.positive_58 y u hy⟩
noncomputable def criticalLSlice_59 : CertifiedSlice :=
 ⟨![0,5,4,3], R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_59, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL009.polynomial_59 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL009.positive_59 y u hy⟩
noncomputable def criticalLSlice_60 : CertifiedSlice :=
 ⟨![0,5,5,2], R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_60, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_60 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL010.positive_60 y u hy⟩
noncomputable def criticalLSlice_61 : CertifiedSlice :=
 ⟨![0,5,6,1], R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_61, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_61 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL010.positive_61 y u hy⟩
noncomputable def criticalLSlice_62 : CertifiedSlice :=
 ⟨![0,5,7,0], R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_62, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_62 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL010.positive_62 y u hy⟩
noncomputable def criticalLSlice_63 : CertifiedSlice :=
 ⟨![0,6,0,6], R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_63, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_63 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL010.positive_63 y u hy⟩
noncomputable def criticalLSlice_64 : CertifiedSlice :=
 ⟨![0,6,1,5], R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_64, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_64 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL010.positive_64 y u hy⟩
noncomputable def criticalLSlice_65 : CertifiedSlice :=
 ⟨![0,6,2,4], R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_65, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL010.polynomial_65 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL010.positive_65 y u hy⟩
noncomputable def criticalLSlice_66 : CertifiedSlice :=
 ⟨![0,6,3,3], R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_66, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_66 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL011.positive_66 y u hy⟩
noncomputable def criticalLSlice_67 : CertifiedSlice :=
 ⟨![0,6,4,2], R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_67, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_67 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL011.positive_67 y u hy⟩
noncomputable def criticalLSlice_68 : CertifiedSlice :=
 ⟨![0,6,5,1], R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_68, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_68 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL011.positive_68 y u hy⟩
noncomputable def criticalLSlice_69 : CertifiedSlice :=
 ⟨![0,6,6,0], R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_69, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_69 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL011.positive_69 y u hy⟩
noncomputable def criticalLSlice_70 : CertifiedSlice :=
 ⟨![0,7,0,5], R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_70, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_70 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL011.positive_70 y u hy⟩
noncomputable def criticalLSlice_71 : CertifiedSlice :=
 ⟨![0,7,1,4], R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_71, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL011.polynomial_71 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL011.positive_71 y u hy⟩
noncomputable def criticalLSlice_72 : CertifiedSlice :=
 ⟨![0,7,2,3], R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_72, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_72 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL012.positive_72 y u hy⟩
noncomputable def criticalLSlice_73 : CertifiedSlice :=
 ⟨![0,7,3,2], R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_73, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_73 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL012.positive_73 y u hy⟩
noncomputable def criticalLSlice_74 : CertifiedSlice :=
 ⟨![0,7,4,1], R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_74, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_74 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL012.positive_74 y u hy⟩
noncomputable def criticalLSlice_75 : CertifiedSlice :=
 ⟨![0,8,0,4], R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_75, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_75 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL012.positive_75 y u hy⟩
noncomputable def criticalLSlice_76 : CertifiedSlice :=
 ⟨![0,8,1,3], R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_76, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_76 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL012.positive_76 y u hy⟩
noncomputable def criticalLSlice_77 : CertifiedSlice :=
 ⟨![0,8,2,2], R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_77, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL012.polynomial_77 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL012.positive_77 y u hy⟩
noncomputable def criticalLSlice_78 : CertifiedSlice :=
 ⟨![0,8,3,1], R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_78, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_78 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL013.positive_78 y u hy⟩
noncomputable def criticalLSlice_79 : CertifiedSlice :=
 ⟨![0,9,0,3], R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_79, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_79 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL013.positive_79 y u hy⟩
noncomputable def criticalLSlice_80 : CertifiedSlice :=
 ⟨![0,9,1,2], R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_80, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_80 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL013.positive_80 y u hy⟩
noncomputable def criticalLSlice_81 : CertifiedSlice :=
 ⟨![0,9,2,1], R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_81, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_81 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL013.positive_81 y u hy⟩
noncomputable def criticalLSlice_82 : CertifiedSlice :=
 ⟨![0,10,0,2], R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_82, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_82 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL013.positive_82 y u hy⟩
noncomputable def criticalLSlice_83 : CertifiedSlice :=
 ⟨![0,10,1,1], R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_83, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL013.polynomial_83 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL013.positive_83 y u hy⟩
noncomputable def criticalLSlice_84 : CertifiedSlice :=
 ⟨![0,11,0,1], R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_84, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_84 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL014.positive_84 y u hy⟩
noncomputable def criticalLSlice_85 : CertifiedSlice :=
 ⟨![1,0,0,11], R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_85, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_85 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL014.positive_85 y u hy⟩
noncomputable def criticalLSlice_86 : CertifiedSlice :=
 ⟨![1,0,1,10], R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_86, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_86 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL014.positive_86 y u hy⟩
noncomputable def criticalLSlice_87 : CertifiedSlice :=
 ⟨![1,0,2,9], R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_87, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_87 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL014.positive_87 y u hy⟩
noncomputable def criticalLSlice_88 : CertifiedSlice :=
 ⟨![1,0,3,8], R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_88, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_88 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL014.positive_88 y u hy⟩
noncomputable def criticalLSlice_89 : CertifiedSlice :=
 ⟨![1,0,4,7], R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_89, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL014.polynomial_89 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL014.positive_89 y u hy⟩
noncomputable def criticalLSlice_90 : CertifiedSlice :=
 ⟨![1,0,5,6], R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_90, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_90 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL015.positive_90 y u hy⟩
noncomputable def criticalLSlice_91 : CertifiedSlice :=
 ⟨![1,0,6,5], R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_91, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_91 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL015.positive_91 y u hy⟩
noncomputable def criticalLSlice_92 : CertifiedSlice :=
 ⟨![1,0,7,4], R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_92, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_92 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL015.positive_92 y u hy⟩
noncomputable def criticalLSlice_93 : CertifiedSlice :=
 ⟨![1,0,8,3], R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_93, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_93 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL015.positive_93 y u hy⟩
noncomputable def criticalLSlice_94 : CertifiedSlice :=
 ⟨![1,0,9,2], R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_94, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_94 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL015.positive_94 y u hy⟩
noncomputable def criticalLSlice_95 : CertifiedSlice :=
 ⟨![1,0,10,1], R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_95, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL015.polynomial_95 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL015.positive_95 y u hy⟩
noncomputable def criticalLSlice_96 : CertifiedSlice :=
 ⟨![1,1,0,10], R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_96, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_96 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL016.positive_96 y u hy⟩
noncomputable def criticalLSlice_97 : CertifiedSlice :=
 ⟨![1,1,1,9], R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_97, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_97 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL016.positive_97 y u hy⟩
noncomputable def criticalLSlice_98 : CertifiedSlice :=
 ⟨![1,1,2,8], R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_98, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_98 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL016.positive_98 y u hy⟩
noncomputable def criticalLSlice_99 : CertifiedSlice :=
 ⟨![1,1,3,7], R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_99, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_99 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL016.positive_99 y u hy⟩
noncomputable def criticalLSlice_100 : CertifiedSlice :=
 ⟨![1,1,4,6], R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_100, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_100 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL016.positive_100 y u hy⟩
noncomputable def criticalLSlice_101 : CertifiedSlice :=
 ⟨![1,1,5,5], R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_101, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL016.polynomial_101 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL016.positive_101 y u hy⟩
noncomputable def criticalLSlice_102 : CertifiedSlice :=
 ⟨![1,1,6,4], R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_102, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_102 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL017.positive_102 y u hy⟩
noncomputable def criticalLSlice_103 : CertifiedSlice :=
 ⟨![1,1,7,3], R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_103, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_103 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL017.positive_103 y u hy⟩
noncomputable def criticalLSlice_104 : CertifiedSlice :=
 ⟨![1,1,8,2], R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_104, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_104 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL017.positive_104 y u hy⟩
noncomputable def criticalLSlice_105 : CertifiedSlice :=
 ⟨![1,1,9,1], R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_105, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_105 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL017.positive_105 y u hy⟩
noncomputable def criticalLSlice_106 : CertifiedSlice :=
 ⟨![1,2,0,9], R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_106, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_106 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL017.positive_106 y u hy⟩
noncomputable def criticalLSlice_107 : CertifiedSlice :=
 ⟨![1,2,1,8], R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_107, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL017.polynomial_107 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL017.positive_107 y u hy⟩
noncomputable def criticalLSlice_108 : CertifiedSlice :=
 ⟨![1,2,2,7], R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_108, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_108 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL018.positive_108 y u hy⟩
noncomputable def criticalLSlice_109 : CertifiedSlice :=
 ⟨![1,2,3,6], R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_109, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_109 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL018.positive_109 y u hy⟩
noncomputable def criticalLSlice_110 : CertifiedSlice :=
 ⟨![1,2,4,5], R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_110, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_110 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL018.positive_110 y u hy⟩
noncomputable def criticalLSlice_111 : CertifiedSlice :=
 ⟨![1,2,5,4], R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_111, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_111 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL018.positive_111 y u hy⟩
noncomputable def criticalLSlice_112 : CertifiedSlice :=
 ⟨![1,2,6,3], R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_112, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_112 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL018.positive_112 y u hy⟩
noncomputable def criticalLSlice_113 : CertifiedSlice :=
 ⟨![1,2,7,2], R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_113, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL018.polynomial_113 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL018.positive_113 y u hy⟩
noncomputable def criticalLSlice_114 : CertifiedSlice :=
 ⟨![1,2,8,1], R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_114, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_114 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL019.positive_114 y u hy⟩
noncomputable def criticalLSlice_115 : CertifiedSlice :=
 ⟨![1,3,0,8], R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_115, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_115 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL019.positive_115 y u hy⟩
noncomputable def criticalLSlice_116 : CertifiedSlice :=
 ⟨![1,3,1,7], R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_116, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_116 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL019.positive_116 y u hy⟩
noncomputable def criticalLSlice_117 : CertifiedSlice :=
 ⟨![1,3,2,6], R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_117, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_117 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL019.positive_117 y u hy⟩
noncomputable def criticalLSlice_118 : CertifiedSlice :=
 ⟨![1,3,3,5], R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_118, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_118 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL019.positive_118 y u hy⟩
noncomputable def criticalLSlice_119 : CertifiedSlice :=
 ⟨![1,3,4,4], R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_119, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL019.polynomial_119 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL019.positive_119 y u hy⟩
noncomputable def criticalLSlice_120 : CertifiedSlice :=
 ⟨![1,3,5,3], R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_120, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_120 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL020.positive_120 y u hy⟩
noncomputable def criticalLSlice_121 : CertifiedSlice :=
 ⟨![1,3,6,2], R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_121, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_121 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL020.positive_121 y u hy⟩
noncomputable def criticalLSlice_122 : CertifiedSlice :=
 ⟨![1,3,7,1], R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_122, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_122 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL020.positive_122 y u hy⟩
noncomputable def criticalLSlice_123 : CertifiedSlice :=
 ⟨![1,4,0,7], R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_123, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_123 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL020.positive_123 y u hy⟩
noncomputable def criticalLSlice_124 : CertifiedSlice :=
 ⟨![1,4,1,6], R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_124, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_124 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL020.positive_124 y u hy⟩
noncomputable def criticalLSlice_125 : CertifiedSlice :=
 ⟨![1,4,2,5], R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_125, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL020.polynomial_125 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL020.positive_125 y u hy⟩
noncomputable def criticalLSlice_126 : CertifiedSlice :=
 ⟨![1,4,3,4], R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_126, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_126 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL021.positive_126 y u hy⟩
noncomputable def criticalLSlice_127 : CertifiedSlice :=
 ⟨![1,4,4,3], R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_127, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_127 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL021.positive_127 y u hy⟩
noncomputable def criticalLSlice_128 : CertifiedSlice :=
 ⟨![1,4,5,2], R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_128, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_128 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL021.positive_128 y u hy⟩
noncomputable def criticalLSlice_129 : CertifiedSlice :=
 ⟨![1,4,6,1], R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_129, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_129 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL021.positive_129 y u hy⟩
noncomputable def criticalLSlice_130 : CertifiedSlice :=
 ⟨![1,5,0,6], R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_130, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_130 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL021.positive_130 y u hy⟩
noncomputable def criticalLSlice_131 : CertifiedSlice :=
 ⟨![1,5,1,5], R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_131, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL021.polynomial_131 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL021.positive_131 y u hy⟩
noncomputable def criticalLSlice_132 : CertifiedSlice :=
 ⟨![1,5,2,4], R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_132, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_132 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL022.positive_132 y u hy⟩
noncomputable def criticalLSlice_133 : CertifiedSlice :=
 ⟨![1,5,3,3], R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_133, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_133 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL022.positive_133 y u hy⟩
noncomputable def criticalLSlice_134 : CertifiedSlice :=
 ⟨![1,5,4,2], R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_134, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_134 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL022.positive_134 y u hy⟩
noncomputable def criticalLSlice_135 : CertifiedSlice :=
 ⟨![1,5,5,1], R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_135, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_135 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL022.positive_135 y u hy⟩
noncomputable def criticalLSlice_136 : CertifiedSlice :=
 ⟨![1,6,0,5], R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_136, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_136 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL022.positive_136 y u hy⟩
noncomputable def criticalLSlice_137 : CertifiedSlice :=
 ⟨![1,6,1,4], R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_137, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL022.polynomial_137 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL022.positive_137 y u hy⟩
noncomputable def criticalLSlice_138 : CertifiedSlice :=
 ⟨![1,6,2,3], R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_138, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_138 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL023.positive_138 y u hy⟩
noncomputable def criticalLSlice_139 : CertifiedSlice :=
 ⟨![1,6,3,2], R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_139, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_139 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL023.positive_139 y u hy⟩
noncomputable def criticalLSlice_140 : CertifiedSlice :=
 ⟨![1,7,0,4], R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_140, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_140 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL023.positive_140 y u hy⟩
noncomputable def criticalLSlice_141 : CertifiedSlice :=
 ⟨![1,7,1,3], R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_141, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_141 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL023.positive_141 y u hy⟩
noncomputable def criticalLSlice_142 : CertifiedSlice :=
 ⟨![1,7,2,2], R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_142, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_142 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL023.positive_142 y u hy⟩
noncomputable def criticalLSlice_143 : CertifiedSlice :=
 ⟨![1,8,0,3], R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_143, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL023.polynomial_143 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL023.positive_143 y u hy⟩
noncomputable def criticalLSlice_144 : CertifiedSlice :=
 ⟨![1,8,1,2], R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_144, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_144 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL024.positive_144 y u hy⟩
noncomputable def criticalLSlice_145 : CertifiedSlice :=
 ⟨![1,9,0,2], R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_145, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_145 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL024.positive_145 y u hy⟩
noncomputable def criticalLSlice_146 : CertifiedSlice :=
 ⟨![2,0,0,10], R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_146, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_146 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL024.positive_146 y u hy⟩
noncomputable def criticalLSlice_147 : CertifiedSlice :=
 ⟨![2,0,1,9], R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_147, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_147 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL024.positive_147 y u hy⟩
noncomputable def criticalLSlice_148 : CertifiedSlice :=
 ⟨![2,0,2,8], R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_148, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_148 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL024.positive_148 y u hy⟩
noncomputable def criticalLSlice_149 : CertifiedSlice :=
 ⟨![2,0,3,7], R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_149, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL024.polynomial_149 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL024.positive_149 y u hy⟩
noncomputable def criticalLSlice_150 : CertifiedSlice :=
 ⟨![2,0,4,6], R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_150, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_150 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL025.positive_150 y u hy⟩
noncomputable def criticalLSlice_151 : CertifiedSlice :=
 ⟨![2,0,5,5], R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_151, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_151 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL025.positive_151 y u hy⟩
noncomputable def criticalLSlice_152 : CertifiedSlice :=
 ⟨![2,0,6,4], R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_152, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_152 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL025.positive_152 y u hy⟩
noncomputable def criticalLSlice_153 : CertifiedSlice :=
 ⟨![2,0,7,3], R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_153, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_153 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL025.positive_153 y u hy⟩
noncomputable def criticalLSlice_154 : CertifiedSlice :=
 ⟨![2,0,8,2], R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_154, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_154 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL025.positive_154 y u hy⟩
noncomputable def criticalLSlice_155 : CertifiedSlice :=
 ⟨![2,1,0,9], R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_155, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL025.polynomial_155 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL025.positive_155 y u hy⟩
noncomputable def criticalLSlice_156 : CertifiedSlice :=
 ⟨![2,1,1,8], R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_156, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_156 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL026.positive_156 y u hy⟩
noncomputable def criticalLSlice_157 : CertifiedSlice :=
 ⟨![2,1,2,7], R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_157, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_157 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL026.positive_157 y u hy⟩
noncomputable def criticalLSlice_158 : CertifiedSlice :=
 ⟨![2,1,3,6], R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_158, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_158 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL026.positive_158 y u hy⟩
noncomputable def criticalLSlice_159 : CertifiedSlice :=
 ⟨![2,1,4,5], R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_159, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_159 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL026.positive_159 y u hy⟩
noncomputable def criticalLSlice_160 : CertifiedSlice :=
 ⟨![2,1,5,4], R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_160, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_160 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL026.positive_160 y u hy⟩
noncomputable def criticalLSlice_161 : CertifiedSlice :=
 ⟨![2,1,6,3], R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_161, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL026.polynomial_161 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL026.positive_161 y u hy⟩
noncomputable def criticalLSlice_162 : CertifiedSlice :=
 ⟨![2,1,7,2], R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_162, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_162 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL027.positive_162 y u hy⟩
noncomputable def criticalLSlice_163 : CertifiedSlice :=
 ⟨![2,2,0,8], R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_163, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_163 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL027.positive_163 y u hy⟩
noncomputable def criticalLSlice_164 : CertifiedSlice :=
 ⟨![2,2,1,7], R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_164, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_164 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL027.positive_164 y u hy⟩
noncomputable def criticalLSlice_165 : CertifiedSlice :=
 ⟨![2,2,2,6], R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_165, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_165 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL027.positive_165 y u hy⟩
noncomputable def criticalLSlice_166 : CertifiedSlice :=
 ⟨![2,2,3,5], R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_166, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_166 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL027.positive_166 y u hy⟩
noncomputable def criticalLSlice_167 : CertifiedSlice :=
 ⟨![2,2,4,4], R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_167, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL027.polynomial_167 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL027.positive_167 y u hy⟩
noncomputable def criticalLSlice_168 : CertifiedSlice :=
 ⟨![2,2,5,3], R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_168, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_168 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL028.positive_168 y u hy⟩
noncomputable def criticalLSlice_169 : CertifiedSlice :=
 ⟨![2,2,6,2], R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_169, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_169 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL028.positive_169 y u hy⟩
noncomputable def criticalLSlice_170 : CertifiedSlice :=
 ⟨![2,3,0,7], R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_170, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_170 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL028.positive_170 y u hy⟩
noncomputable def criticalLSlice_171 : CertifiedSlice :=
 ⟨![2,3,1,6], R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_171, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_171 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL028.positive_171 y u hy⟩
noncomputable def criticalLSlice_172 : CertifiedSlice :=
 ⟨![2,3,2,5], R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_172, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_172 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL028.positive_172 y u hy⟩
noncomputable def criticalLSlice_173 : CertifiedSlice :=
 ⟨![2,3,3,4], R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_173, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL028.polynomial_173 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL028.positive_173 y u hy⟩
noncomputable def criticalLSlice_174 : CertifiedSlice :=
 ⟨![2,3,4,3], R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_174, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_174 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL029.positive_174 y u hy⟩
noncomputable def criticalLSlice_175 : CertifiedSlice :=
 ⟨![2,3,5,2], R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_175, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_175 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL029.positive_175 y u hy⟩
noncomputable def criticalLSlice_176 : CertifiedSlice :=
 ⟨![2,4,0,6], R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_176, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_176 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL029.positive_176 y u hy⟩
noncomputable def criticalLSlice_177 : CertifiedSlice :=
 ⟨![2,4,1,5], R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_177, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_177 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL029.positive_177 y u hy⟩
noncomputable def criticalLSlice_178 : CertifiedSlice :=
 ⟨![2,4,2,4], R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_178, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_178 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL029.positive_178 y u hy⟩
noncomputable def criticalLSlice_179 : CertifiedSlice :=
 ⟨![2,4,3,3], R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_179, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL029.polynomial_179 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL029.positive_179 y u hy⟩
noncomputable def criticalLSlice_180 : CertifiedSlice :=
 ⟨![2,4,4,2], R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_180, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_180 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL030.positive_180 y u hy⟩
noncomputable def criticalLSlice_181 : CertifiedSlice :=
 ⟨![2,5,0,5], R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_181, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_181 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL030.positive_181 y u hy⟩
noncomputable def criticalLSlice_182 : CertifiedSlice :=
 ⟨![2,5,1,4], R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_182, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_182 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL030.positive_182 y u hy⟩
noncomputable def criticalLSlice_183 : CertifiedSlice :=
 ⟨![2,5,2,3], R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_183, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_183 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL030.positive_183 y u hy⟩
noncomputable def criticalLSlice_184 : CertifiedSlice :=
 ⟨![2,6,0,4], R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_184, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_184 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL030.positive_184 y u hy⟩
noncomputable def criticalLSlice_185 : CertifiedSlice :=
 ⟨![2,6,1,3], R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_185, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL030.polynomial_185 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL030.positive_185 y u hy⟩
noncomputable def criticalLSlice_186 : CertifiedSlice :=
 ⟨![2,7,0,3], R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_186, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_186 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL031.positive_186 y u hy⟩
noncomputable def criticalLSlice_187 : CertifiedSlice :=
 ⟨![3,0,0,9], R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_187, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_187 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL031.positive_187 y u hy⟩
noncomputable def criticalLSlice_188 : CertifiedSlice :=
 ⟨![3,0,1,8], R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_188, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_188 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL031.positive_188 y u hy⟩
noncomputable def criticalLSlice_189 : CertifiedSlice :=
 ⟨![3,0,2,7], R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_189, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_189 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL031.positive_189 y u hy⟩
noncomputable def criticalLSlice_190 : CertifiedSlice :=
 ⟨![3,0,3,6], R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_190, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_190 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL031.positive_190 y u hy⟩
noncomputable def criticalLSlice_191 : CertifiedSlice :=
 ⟨![3,0,4,5], R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_191, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL031.polynomial_191 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL031.positive_191 y u hy⟩
noncomputable def criticalLSlice_192 : CertifiedSlice :=
 ⟨![3,0,5,4], R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_192, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_192 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL032.positive_192 y u hy⟩
noncomputable def criticalLSlice_193 : CertifiedSlice :=
 ⟨![3,0,6,3], R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_193, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_193 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL032.positive_193 y u hy⟩
noncomputable def criticalLSlice_194 : CertifiedSlice :=
 ⟨![3,1,0,8], R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_194, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_194 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL032.positive_194 y u hy⟩
noncomputable def criticalLSlice_195 : CertifiedSlice :=
 ⟨![3,1,1,7], R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_195, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_195 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL032.positive_195 y u hy⟩
noncomputable def criticalLSlice_196 : CertifiedSlice :=
 ⟨![3,1,2,6], R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_196, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_196 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL032.positive_196 y u hy⟩
noncomputable def criticalLSlice_197 : CertifiedSlice :=
 ⟨![3,1,3,5], R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_197, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL032.polynomial_197 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL032.positive_197 y u hy⟩
noncomputable def criticalLSlice_198 : CertifiedSlice :=
 ⟨![3,1,4,4], R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_198, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_198 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL033.positive_198 y u hy⟩
noncomputable def criticalLSlice_199 : CertifiedSlice :=
 ⟨![3,1,5,3], R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_199, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_199 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL033.positive_199 y u hy⟩
noncomputable def criticalLSlice_200 : CertifiedSlice :=
 ⟨![3,2,0,7], R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_200, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_200 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL033.positive_200 y u hy⟩
noncomputable def criticalLSlice_201 : CertifiedSlice :=
 ⟨![3,2,1,6], R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_201, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_201 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL033.positive_201 y u hy⟩
noncomputable def criticalLSlice_202 : CertifiedSlice :=
 ⟨![3,2,2,5], R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_202, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_202 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL033.positive_202 y u hy⟩
noncomputable def criticalLSlice_203 : CertifiedSlice :=
 ⟨![3,2,3,4], R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_203, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL033.polynomial_203 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL033.positive_203 y u hy⟩
noncomputable def criticalLSlice_204 : CertifiedSlice :=
 ⟨![3,2,4,3], R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_204, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_204 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL034.positive_204 y u hy⟩
noncomputable def criticalLSlice_205 : CertifiedSlice :=
 ⟨![3,3,0,6], R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_205, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_205 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL034.positive_205 y u hy⟩
noncomputable def criticalLSlice_206 : CertifiedSlice :=
 ⟨![3,3,1,5], R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_206, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_206 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL034.positive_206 y u hy⟩
noncomputable def criticalLSlice_207 : CertifiedSlice :=
 ⟨![3,3,2,4], R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_207, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_207 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL034.positive_207 y u hy⟩
noncomputable def criticalLSlice_208 : CertifiedSlice :=
 ⟨![3,3,3,3], R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_208, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_208 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL034.positive_208 y u hy⟩
noncomputable def criticalLSlice_209 : CertifiedSlice :=
 ⟨![3,4,0,5], R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_209, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL034.polynomial_209 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL034.positive_209 y u hy⟩
noncomputable def criticalLSlice_210 : CertifiedSlice :=
 ⟨![3,4,1,4], R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_210, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_210 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL035.positive_210 y u hy⟩
noncomputable def criticalLSlice_211 : CertifiedSlice :=
 ⟨![3,5,0,4], R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_211, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_211 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL035.positive_211 y u hy⟩
noncomputable def criticalLSlice_212 : CertifiedSlice :=
 ⟨![4,0,0,8], R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_212, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_212 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL035.positive_212 y u hy⟩
noncomputable def criticalLSlice_213 : CertifiedSlice :=
 ⟨![4,0,1,7], R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_213, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_213 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL035.positive_213 y u hy⟩
noncomputable def criticalLSlice_214 : CertifiedSlice :=
 ⟨![4,0,2,6], R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_214, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_214 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL035.positive_214 y u hy⟩
noncomputable def criticalLSlice_215 : CertifiedSlice :=
 ⟨![4,0,3,5], R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_215, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL035.polynomial_215 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL035.positive_215 y u hy⟩
noncomputable def criticalLSlice_216 : CertifiedSlice :=
 ⟨![4,0,4,4], R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_216, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_216 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL036.positive_216 y u hy⟩
noncomputable def criticalLSlice_217 : CertifiedSlice :=
 ⟨![4,1,0,7], R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_217, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_217 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL036.positive_217 y u hy⟩
noncomputable def criticalLSlice_218 : CertifiedSlice :=
 ⟨![4,1,1,6], R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_218, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_218 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL036.positive_218 y u hy⟩
noncomputable def criticalLSlice_219 : CertifiedSlice :=
 ⟨![4,1,2,5], R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_219, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_219 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL036.positive_219 y u hy⟩
noncomputable def criticalLSlice_220 : CertifiedSlice :=
 ⟨![4,1,3,4], R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_220, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_220 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL036.positive_220 y u hy⟩
noncomputable def criticalLSlice_221 : CertifiedSlice :=
 ⟨![4,2,0,6], R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_221, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL036.polynomial_221 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL036.positive_221 y u hy⟩
noncomputable def criticalLSlice_222 : CertifiedSlice :=
 ⟨![4,2,1,5], R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_222, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_222 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL037.positive_222 y u hy⟩
noncomputable def criticalLSlice_223 : CertifiedSlice :=
 ⟨![4,2,2,4], R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_223, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_223 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL037.positive_223 y u hy⟩
noncomputable def criticalLSlice_224 : CertifiedSlice :=
 ⟨![4,3,0,5], R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_224, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_224 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL037.positive_224 y u hy⟩
noncomputable def criticalLSlice_225 : CertifiedSlice :=
 ⟨![5,0,0,7], R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_225, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_225 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL037.positive_225 y u hy⟩
noncomputable def criticalLSlice_226 : CertifiedSlice :=
 ⟨![5,0,1,6], R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_226, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_226 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL037.positive_226 y u hy⟩
noncomputable def criticalLSlice_227 : CertifiedSlice :=
 ⟨![5,0,2,5], R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_227, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL037.polynomial_227 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL037.positive_227 y u hy⟩
noncomputable def criticalLSlice_228 : CertifiedSlice :=
 ⟨![5,1,0,6], R7.Core.SpectralSliceCertificates.CriticalL038.polynomial_228, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL038.polynomial_228 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL038.positive_228 y u hy⟩
noncomputable def criticalLSlice_229 : CertifiedSlice :=
 ⟨![5,1,1,5], R7.Core.SpectralSliceCertificates.CriticalL038.polynomial_229, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL038.polynomial_229 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL038.positive_229 y u hy⟩
noncomputable def criticalLSlice_230 : CertifiedSlice :=
 ⟨![6,0,0,6], R7.Core.SpectralSliceCertificates.CriticalL038.polynomial_230, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 13, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalL038.polynomial_230 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalL038.positive_230 y u hy⟩
noncomputable def criticalLCertified : List CertifiedSlice := [
 criticalLSlice_0,
 criticalLSlice_1,
 criticalLSlice_2,
 criticalLSlice_3,
 criticalLSlice_4,
 criticalLSlice_5,
 criticalLSlice_6,
 criticalLSlice_7,
 criticalLSlice_8,
 criticalLSlice_9,
 criticalLSlice_10,
 criticalLSlice_11,
 criticalLSlice_12,
 criticalLSlice_13,
 criticalLSlice_14,
 criticalLSlice_15,
 criticalLSlice_16,
 criticalLSlice_17,
 criticalLSlice_18,
 criticalLSlice_19,
 criticalLSlice_20,
 criticalLSlice_21,
 criticalLSlice_22,
 criticalLSlice_23,
 criticalLSlice_24,
 criticalLSlice_25,
 criticalLSlice_26,
 criticalLSlice_27,
 criticalLSlice_28,
 criticalLSlice_29,
 criticalLSlice_30,
 criticalLSlice_31,
 criticalLSlice_32,
 criticalLSlice_33,
 criticalLSlice_34,
 criticalLSlice_35,
 criticalLSlice_36,
 criticalLSlice_37,
 criticalLSlice_38,
 criticalLSlice_39,
 criticalLSlice_40,
 criticalLSlice_41,
 criticalLSlice_42,
 criticalLSlice_43,
 criticalLSlice_44,
 criticalLSlice_45,
 criticalLSlice_46,
 criticalLSlice_47,
 criticalLSlice_48,
 criticalLSlice_49,
 criticalLSlice_50,
 criticalLSlice_51,
 criticalLSlice_52,
 criticalLSlice_53,
 criticalLSlice_54,
 criticalLSlice_55,
 criticalLSlice_56,
 criticalLSlice_57,
 criticalLSlice_58,
 criticalLSlice_59,
 criticalLSlice_60,
 criticalLSlice_61,
 criticalLSlice_62,
 criticalLSlice_63,
 criticalLSlice_64,
 criticalLSlice_65,
 criticalLSlice_66,
 criticalLSlice_67,
 criticalLSlice_68,
 criticalLSlice_69,
 criticalLSlice_70,
 criticalLSlice_71,
 criticalLSlice_72,
 criticalLSlice_73,
 criticalLSlice_74,
 CertifiedSlice.reflected ![0,7,5,0] (criticalLSlice_62),
 criticalLSlice_75,
 criticalLSlice_76,
 criticalLSlice_77,
 criticalLSlice_78,
 CertifiedSlice.reflected ![0,8,4,0] (criticalLSlice_54),
 criticalLSlice_79,
 criticalLSlice_80,
 criticalLSlice_81,
 CertifiedSlice.reflected ![0,9,3,0] (criticalLSlice_45),
 criticalLSlice_82,
 criticalLSlice_83,
 CertifiedSlice.reflected ![0,10,2,0] (criticalLSlice_35),
 criticalLSlice_84,
 CertifiedSlice.reflected ![0,11,1,0] (criticalLSlice_24),
 CertifiedSlice.reflected ![0,12,0,0] (criticalLSlice_12),
 criticalLSlice_85,
 criticalLSlice_86,
 criticalLSlice_87,
 criticalLSlice_88,
 criticalLSlice_89,
 criticalLSlice_90,
 criticalLSlice_91,
 criticalLSlice_92,
 criticalLSlice_93,
 criticalLSlice_94,
 criticalLSlice_95,
 CertifiedSlice.reflected ![1,0,11,0] (criticalLSlice_84),
 criticalLSlice_96,
 criticalLSlice_97,
 criticalLSlice_98,
 criticalLSlice_99,
 criticalLSlice_100,
 criticalLSlice_101,
 criticalLSlice_102,
 criticalLSlice_103,
 criticalLSlice_104,
 criticalLSlice_105,
 CertifiedSlice.reflected ![1,1,10,0] (criticalLSlice_83),
 criticalLSlice_106,
 criticalLSlice_107,
 criticalLSlice_108,
 criticalLSlice_109,
 criticalLSlice_110,
 criticalLSlice_111,
 criticalLSlice_112,
 criticalLSlice_113,
 criticalLSlice_114,
 CertifiedSlice.reflected ![1,2,9,0] (criticalLSlice_81),
 criticalLSlice_115,
 criticalLSlice_116,
 criticalLSlice_117,
 criticalLSlice_118,
 criticalLSlice_119,
 criticalLSlice_120,
 criticalLSlice_121,
 criticalLSlice_122,
 CertifiedSlice.reflected ![1,3,8,0] (criticalLSlice_78),
 criticalLSlice_123,
 criticalLSlice_124,
 criticalLSlice_125,
 criticalLSlice_126,
 criticalLSlice_127,
 criticalLSlice_128,
 criticalLSlice_129,
 CertifiedSlice.reflected ![1,4,7,0] (criticalLSlice_74),
 criticalLSlice_130,
 criticalLSlice_131,
 criticalLSlice_132,
 criticalLSlice_133,
 criticalLSlice_134,
 criticalLSlice_135,
 CertifiedSlice.reflected ![1,5,6,0] (criticalLSlice_68),
 criticalLSlice_136,
 criticalLSlice_137,
 criticalLSlice_138,
 criticalLSlice_139,
 CertifiedSlice.reflected ![1,6,4,1] (criticalLSlice_129),
 CertifiedSlice.reflected ![1,6,5,0] (criticalLSlice_61),
 criticalLSlice_140,
 criticalLSlice_141,
 criticalLSlice_142,
 CertifiedSlice.reflected ![1,7,3,1] (criticalLSlice_122),
 CertifiedSlice.reflected ![1,7,4,0] (criticalLSlice_53),
 criticalLSlice_143,
 criticalLSlice_144,
 CertifiedSlice.reflected ![1,8,2,1] (criticalLSlice_114),
 CertifiedSlice.reflected ![1,8,3,0] (criticalLSlice_44),
 criticalLSlice_145,
 CertifiedSlice.reflected ![1,9,1,1] (criticalLSlice_105),
 CertifiedSlice.reflected ![1,9,2,0] (criticalLSlice_34),
 CertifiedSlice.reflected ![1,10,0,1] (criticalLSlice_95),
 CertifiedSlice.reflected ![1,10,1,0] (criticalLSlice_23),
 CertifiedSlice.reflected ![1,11,0,0] (criticalLSlice_11),
 criticalLSlice_146,
 criticalLSlice_147,
 criticalLSlice_148,
 criticalLSlice_149,
 criticalLSlice_150,
 criticalLSlice_151,
 criticalLSlice_152,
 criticalLSlice_153,
 criticalLSlice_154,
 CertifiedSlice.reflected ![2,0,9,1] (criticalLSlice_145),
 CertifiedSlice.reflected ![2,0,10,0] (criticalLSlice_82),
 criticalLSlice_155,
 criticalLSlice_156,
 criticalLSlice_157,
 criticalLSlice_158,
 criticalLSlice_159,
 criticalLSlice_160,
 criticalLSlice_161,
 criticalLSlice_162,
 CertifiedSlice.reflected ![2,1,8,1] (criticalLSlice_144),
 CertifiedSlice.reflected ![2,1,9,0] (criticalLSlice_80),
 criticalLSlice_163,
 criticalLSlice_164,
 criticalLSlice_165,
 criticalLSlice_166,
 criticalLSlice_167,
 criticalLSlice_168,
 criticalLSlice_169,
 CertifiedSlice.reflected ![2,2,7,1] (criticalLSlice_142),
 CertifiedSlice.reflected ![2,2,8,0] (criticalLSlice_77),
 criticalLSlice_170,
 criticalLSlice_171,
 criticalLSlice_172,
 criticalLSlice_173,
 criticalLSlice_174,
 criticalLSlice_175,
 CertifiedSlice.reflected ![2,3,6,1] (criticalLSlice_139),
 CertifiedSlice.reflected ![2,3,7,0] (criticalLSlice_73),
 criticalLSlice_176,
 criticalLSlice_177,
 criticalLSlice_178,
 criticalLSlice_179,
 criticalLSlice_180,
 CertifiedSlice.reflected ![2,4,5,1] (criticalLSlice_134),
 CertifiedSlice.reflected ![2,4,6,0] (criticalLSlice_67),
 criticalLSlice_181,
 criticalLSlice_182,
 criticalLSlice_183,
 CertifiedSlice.reflected ![2,5,3,2] (criticalLSlice_175),
 CertifiedSlice.reflected ![2,5,4,1] (criticalLSlice_128),
 CertifiedSlice.reflected ![2,5,5,0] (criticalLSlice_60),
 criticalLSlice_184,
 criticalLSlice_185,
 CertifiedSlice.reflected ![2,6,2,2] (criticalLSlice_169),
 CertifiedSlice.reflected ![2,6,3,1] (criticalLSlice_121),
 CertifiedSlice.reflected ![2,6,4,0] (criticalLSlice_52),
 criticalLSlice_186,
 CertifiedSlice.reflected ![2,7,1,2] (criticalLSlice_162),
 CertifiedSlice.reflected ![2,7,2,1] (criticalLSlice_113),
 CertifiedSlice.reflected ![2,7,3,0] (criticalLSlice_43),
 CertifiedSlice.reflected ![2,8,0,2] (criticalLSlice_154),
 CertifiedSlice.reflected ![2,8,1,1] (criticalLSlice_104),
 CertifiedSlice.reflected ![2,8,2,0] (criticalLSlice_33),
 CertifiedSlice.reflected ![2,9,0,1] (criticalLSlice_94),
 CertifiedSlice.reflected ![2,9,1,0] (criticalLSlice_22),
 CertifiedSlice.reflected ![2,10,0,0] (criticalLSlice_10),
 criticalLSlice_187,
 criticalLSlice_188,
 criticalLSlice_189,
 criticalLSlice_190,
 criticalLSlice_191,
 criticalLSlice_192,
 criticalLSlice_193,
 CertifiedSlice.reflected ![3,0,7,2] (criticalLSlice_186),
 CertifiedSlice.reflected ![3,0,8,1] (criticalLSlice_143),
 CertifiedSlice.reflected ![3,0,9,0] (criticalLSlice_79),
 criticalLSlice_194,
 criticalLSlice_195,
 criticalLSlice_196,
 criticalLSlice_197,
 criticalLSlice_198,
 criticalLSlice_199,
 CertifiedSlice.reflected ![3,1,6,2] (criticalLSlice_185),
 CertifiedSlice.reflected ![3,1,7,1] (criticalLSlice_141),
 CertifiedSlice.reflected ![3,1,8,0] (criticalLSlice_76),
 criticalLSlice_200,
 criticalLSlice_201,
 criticalLSlice_202,
 criticalLSlice_203,
 criticalLSlice_204,
 CertifiedSlice.reflected ![3,2,5,2] (criticalLSlice_183),
 CertifiedSlice.reflected ![3,2,6,1] (criticalLSlice_138),
 CertifiedSlice.reflected ![3,2,7,0] (criticalLSlice_72),
 criticalLSlice_205,
 criticalLSlice_206,
 criticalLSlice_207,
 criticalLSlice_208,
 CertifiedSlice.reflected ![3,3,4,2] (criticalLSlice_179),
 CertifiedSlice.reflected ![3,3,5,1] (criticalLSlice_133),
 CertifiedSlice.reflected ![3,3,6,0] (criticalLSlice_66),
 criticalLSlice_209,
 criticalLSlice_210,
 CertifiedSlice.reflected ![3,4,2,3] (criticalLSlice_204),
 CertifiedSlice.reflected ![3,4,3,2] (criticalLSlice_174),
 CertifiedSlice.reflected ![3,4,4,1] (criticalLSlice_127),
 CertifiedSlice.reflected ![3,4,5,0] (criticalLSlice_59),
 criticalLSlice_211,
 CertifiedSlice.reflected ![3,5,1,3] (criticalLSlice_199),
 CertifiedSlice.reflected ![3,5,2,2] (criticalLSlice_168),
 CertifiedSlice.reflected ![3,5,3,1] (criticalLSlice_120),
 CertifiedSlice.reflected ![3,5,4,0] (criticalLSlice_51),
 CertifiedSlice.reflected ![3,6,0,3] (criticalLSlice_193),
 CertifiedSlice.reflected ![3,6,1,2] (criticalLSlice_161),
 CertifiedSlice.reflected ![3,6,2,1] (criticalLSlice_112),
 CertifiedSlice.reflected ![3,6,3,0] (criticalLSlice_42),
 CertifiedSlice.reflected ![3,7,0,2] (criticalLSlice_153),
 CertifiedSlice.reflected ![3,7,1,1] (criticalLSlice_103),
 CertifiedSlice.reflected ![3,7,2,0] (criticalLSlice_32),
 CertifiedSlice.reflected ![3,8,0,1] (criticalLSlice_93),
 CertifiedSlice.reflected ![3,8,1,0] (criticalLSlice_21),
 CertifiedSlice.reflected ![3,9,0,0] (criticalLSlice_9),
 criticalLSlice_212,
 criticalLSlice_213,
 criticalLSlice_214,
 criticalLSlice_215,
 criticalLSlice_216,
 CertifiedSlice.reflected ![4,0,5,3] (criticalLSlice_211),
 CertifiedSlice.reflected ![4,0,6,2] (criticalLSlice_184),
 CertifiedSlice.reflected ![4,0,7,1] (criticalLSlice_140),
 CertifiedSlice.reflected ![4,0,8,0] (criticalLSlice_75),
 criticalLSlice_217,
 criticalLSlice_218,
 criticalLSlice_219,
 criticalLSlice_220,
 CertifiedSlice.reflected ![4,1,4,3] (criticalLSlice_210),
 CertifiedSlice.reflected ![4,1,5,2] (criticalLSlice_182),
 CertifiedSlice.reflected ![4,1,6,1] (criticalLSlice_137),
 CertifiedSlice.reflected ![4,1,7,0] (criticalLSlice_71),
 criticalLSlice_221,
 criticalLSlice_222,
 criticalLSlice_223,
 CertifiedSlice.reflected ![4,2,3,3] (criticalLSlice_207),
 CertifiedSlice.reflected ![4,2,4,2] (criticalLSlice_178),
 CertifiedSlice.reflected ![4,2,5,1] (criticalLSlice_132),
 CertifiedSlice.reflected ![4,2,6,0] (criticalLSlice_65),
 criticalLSlice_224,
 CertifiedSlice.reflected ![4,3,1,4] (criticalLSlice_220),
 CertifiedSlice.reflected ![4,3,2,3] (criticalLSlice_203),
 CertifiedSlice.reflected ![4,3,3,2] (criticalLSlice_173),
 CertifiedSlice.reflected ![4,3,4,1] (criticalLSlice_126),
 CertifiedSlice.reflected ![4,3,5,0] (criticalLSlice_58),
 CertifiedSlice.reflected ![4,4,0,4] (criticalLSlice_216),
 CertifiedSlice.reflected ![4,4,1,3] (criticalLSlice_198),
 CertifiedSlice.reflected ![4,4,2,2] (criticalLSlice_167),
 CertifiedSlice.reflected ![4,4,3,1] (criticalLSlice_119),
 CertifiedSlice.reflected ![4,4,4,0] (criticalLSlice_50),
 CertifiedSlice.reflected ![4,5,0,3] (criticalLSlice_192),
 CertifiedSlice.reflected ![4,5,1,2] (criticalLSlice_160),
 CertifiedSlice.reflected ![4,5,2,1] (criticalLSlice_111),
 CertifiedSlice.reflected ![4,5,3,0] (criticalLSlice_41),
 CertifiedSlice.reflected ![4,6,0,2] (criticalLSlice_152),
 CertifiedSlice.reflected ![4,6,1,1] (criticalLSlice_102),
 CertifiedSlice.reflected ![4,6,2,0] (criticalLSlice_31),
 CertifiedSlice.reflected ![4,7,0,1] (criticalLSlice_92),
 CertifiedSlice.reflected ![4,7,1,0] (criticalLSlice_20),
 CertifiedSlice.reflected ![4,8,0,0] (criticalLSlice_8),
 criticalLSlice_225,
 criticalLSlice_226,
 criticalLSlice_227,
 CertifiedSlice.reflected ![5,0,3,4] (criticalLSlice_224),
 CertifiedSlice.reflected ![5,0,4,3] (criticalLSlice_209),
 CertifiedSlice.reflected ![5,0,5,2] (criticalLSlice_181),
 CertifiedSlice.reflected ![5,0,6,1] (criticalLSlice_136),
 CertifiedSlice.reflected ![5,0,7,0] (criticalLSlice_70),
 criticalLSlice_228,
 criticalLSlice_229,
 CertifiedSlice.reflected ![5,1,2,4] (criticalLSlice_222),
 CertifiedSlice.reflected ![5,1,3,3] (criticalLSlice_206),
 CertifiedSlice.reflected ![5,1,4,2] (criticalLSlice_177),
 CertifiedSlice.reflected ![5,1,5,1] (criticalLSlice_131),
 CertifiedSlice.reflected ![5,1,6,0] (criticalLSlice_64),
 CertifiedSlice.reflected ![5,2,0,5] (criticalLSlice_227),
 CertifiedSlice.reflected ![5,2,1,4] (criticalLSlice_219),
 CertifiedSlice.reflected ![5,2,2,3] (criticalLSlice_202),
 CertifiedSlice.reflected ![5,2,3,2] (criticalLSlice_172),
 CertifiedSlice.reflected ![5,2,4,1] (criticalLSlice_125),
 CertifiedSlice.reflected ![5,2,5,0] (criticalLSlice_57),
 CertifiedSlice.reflected ![5,3,0,4] (criticalLSlice_215),
 CertifiedSlice.reflected ![5,3,1,3] (criticalLSlice_197),
 CertifiedSlice.reflected ![5,3,2,2] (criticalLSlice_166),
 CertifiedSlice.reflected ![5,3,3,1] (criticalLSlice_118),
 CertifiedSlice.reflected ![5,3,4,0] (criticalLSlice_49),
 CertifiedSlice.reflected ![5,4,0,3] (criticalLSlice_191),
 CertifiedSlice.reflected ![5,4,1,2] (criticalLSlice_159),
 CertifiedSlice.reflected ![5,4,2,1] (criticalLSlice_110),
 CertifiedSlice.reflected ![5,4,3,0] (criticalLSlice_40),
 CertifiedSlice.reflected ![5,5,0,2] (criticalLSlice_151),
 CertifiedSlice.reflected ![5,5,1,1] (criticalLSlice_101),
 CertifiedSlice.reflected ![5,5,2,0] (criticalLSlice_30),
 CertifiedSlice.reflected ![5,6,0,1] (criticalLSlice_91),
 CertifiedSlice.reflected ![5,6,1,0] (criticalLSlice_19),
 CertifiedSlice.reflected ![5,7,0,0] (criticalLSlice_7),
 criticalLSlice_230,
 CertifiedSlice.reflected ![6,0,1,5] (criticalLSlice_228),
 CertifiedSlice.reflected ![6,0,2,4] (criticalLSlice_221),
 CertifiedSlice.reflected ![6,0,3,3] (criticalLSlice_205),
 CertifiedSlice.reflected ![6,0,4,2] (criticalLSlice_176),
 CertifiedSlice.reflected ![6,0,5,1] (criticalLSlice_130),
 CertifiedSlice.reflected ![6,0,6,0] (criticalLSlice_63),
 CertifiedSlice.reflected ![6,1,0,5] (criticalLSlice_226),
 CertifiedSlice.reflected ![6,1,1,4] (criticalLSlice_218),
 CertifiedSlice.reflected ![6,1,2,3] (criticalLSlice_201),
 CertifiedSlice.reflected ![6,1,3,2] (criticalLSlice_171),
 CertifiedSlice.reflected ![6,1,4,1] (criticalLSlice_124),
 CertifiedSlice.reflected ![6,1,5,0] (criticalLSlice_56),
 CertifiedSlice.reflected ![6,2,0,4] (criticalLSlice_214),
 CertifiedSlice.reflected ![6,2,1,3] (criticalLSlice_196),
 CertifiedSlice.reflected ![6,2,2,2] (criticalLSlice_165),
 CertifiedSlice.reflected ![6,2,3,1] (criticalLSlice_117),
 CertifiedSlice.reflected ![6,2,4,0] (criticalLSlice_48),
 CertifiedSlice.reflected ![6,3,0,3] (criticalLSlice_190),
 CertifiedSlice.reflected ![6,3,1,2] (criticalLSlice_158),
 CertifiedSlice.reflected ![6,3,2,1] (criticalLSlice_109),
 CertifiedSlice.reflected ![6,3,3,0] (criticalLSlice_39),
 CertifiedSlice.reflected ![6,4,0,2] (criticalLSlice_150),
 CertifiedSlice.reflected ![6,4,1,1] (criticalLSlice_100),
 CertifiedSlice.reflected ![6,4,2,0] (criticalLSlice_29),
 CertifiedSlice.reflected ![6,5,0,1] (criticalLSlice_90),
 CertifiedSlice.reflected ![6,5,1,0] (criticalLSlice_18),
 CertifiedSlice.reflected ![6,6,0,0] (criticalLSlice_6),
 CertifiedSlice.reflected ![7,0,0,5] (criticalLSlice_225),
 CertifiedSlice.reflected ![7,0,1,4] (criticalLSlice_217),
 CertifiedSlice.reflected ![7,0,2,3] (criticalLSlice_200),
 CertifiedSlice.reflected ![7,0,3,2] (criticalLSlice_170),
 CertifiedSlice.reflected ![7,0,4,1] (criticalLSlice_123),
 CertifiedSlice.reflected ![7,0,5,0] (criticalLSlice_55),
 CertifiedSlice.reflected ![7,1,0,4] (criticalLSlice_213),
 CertifiedSlice.reflected ![7,1,1,3] (criticalLSlice_195),
 CertifiedSlice.reflected ![7,1,2,2] (criticalLSlice_164),
 CertifiedSlice.reflected ![7,1,3,1] (criticalLSlice_116),
 CertifiedSlice.reflected ![7,1,4,0] (criticalLSlice_47),
 CertifiedSlice.reflected ![7,2,0,3] (criticalLSlice_189),
 CertifiedSlice.reflected ![7,2,1,2] (criticalLSlice_157),
 CertifiedSlice.reflected ![7,2,2,1] (criticalLSlice_108),
 CertifiedSlice.reflected ![7,2,3,0] (criticalLSlice_38),
 CertifiedSlice.reflected ![7,3,0,2] (criticalLSlice_149),
 CertifiedSlice.reflected ![7,3,1,1] (criticalLSlice_99),
 CertifiedSlice.reflected ![7,3,2,0] (criticalLSlice_28),
 CertifiedSlice.reflected ![7,4,0,1] (criticalLSlice_89),
 CertifiedSlice.reflected ![7,4,1,0] (criticalLSlice_17),
 CertifiedSlice.reflected ![7,5,0,0] (criticalLSlice_5),
 CertifiedSlice.reflected ![8,0,0,4] (criticalLSlice_212),
 CertifiedSlice.reflected ![8,0,1,3] (criticalLSlice_194),
 CertifiedSlice.reflected ![8,0,2,2] (criticalLSlice_163),
 CertifiedSlice.reflected ![8,0,3,1] (criticalLSlice_115),
 CertifiedSlice.reflected ![8,0,4,0] (criticalLSlice_46),
 CertifiedSlice.reflected ![8,1,0,3] (criticalLSlice_188),
 CertifiedSlice.reflected ![8,1,1,2] (criticalLSlice_156),
 CertifiedSlice.reflected ![8,1,2,1] (criticalLSlice_107),
 CertifiedSlice.reflected ![8,1,3,0] (criticalLSlice_37),
 CertifiedSlice.reflected ![8,2,0,2] (criticalLSlice_148),
 CertifiedSlice.reflected ![8,2,1,1] (criticalLSlice_98),
 CertifiedSlice.reflected ![8,2,2,0] (criticalLSlice_27),
 CertifiedSlice.reflected ![8,3,0,1] (criticalLSlice_88),
 CertifiedSlice.reflected ![8,3,1,0] (criticalLSlice_16),
 CertifiedSlice.reflected ![8,4,0,0] (criticalLSlice_4),
 CertifiedSlice.reflected ![9,0,0,3] (criticalLSlice_187),
 CertifiedSlice.reflected ![9,0,1,2] (criticalLSlice_155),
 CertifiedSlice.reflected ![9,0,2,1] (criticalLSlice_106),
 CertifiedSlice.reflected ![9,0,3,0] (criticalLSlice_36),
 CertifiedSlice.reflected ![9,1,0,2] (criticalLSlice_147),
 CertifiedSlice.reflected ![9,1,1,1] (criticalLSlice_97),
 CertifiedSlice.reflected ![9,1,2,0] (criticalLSlice_26),
 CertifiedSlice.reflected ![9,2,0,1] (criticalLSlice_87),
 CertifiedSlice.reflected ![9,2,1,0] (criticalLSlice_15),
 CertifiedSlice.reflected ![9,3,0,0] (criticalLSlice_3),
 CertifiedSlice.reflected ![10,0,0,2] (criticalLSlice_146),
 CertifiedSlice.reflected ![10,0,1,1] (criticalLSlice_96),
 CertifiedSlice.reflected ![10,0,2,0] (criticalLSlice_25),
 CertifiedSlice.reflected ![10,1,0,1] (criticalLSlice_86),
 CertifiedSlice.reflected ![10,1,1,0] (criticalLSlice_14),
 CertifiedSlice.reflected ![10,2,0,0] (criticalLSlice_2),
 CertifiedSlice.reflected ![11,0,0,1] (criticalLSlice_85),
 CertifiedSlice.reflected ![11,0,1,0] (criticalLSlice_13),
 CertifiedSlice.reflected ![11,1,0,0] (criticalLSlice_1),
 CertifiedSlice.reflected ![12,0,0,0] (criticalLSlice_0)
]
noncomputable def criticalLGroups : Groups := criticalLCertified.map CertifiedSlice.row
theorem criticalLGroups_positive (row) (hrow : row ∈ criticalLGroups) (u y : ℝ) (hy : 0 ≤ y) :
 0 < eval row.2 u y := certifiedRows_positive criticalLCertified row hrow u y hy
theorem criticalLGroups_short : ∀ row ∈ criticalLGroups, ∀ a ∈ row.2, a.length ≤ 3 := by
 decide +kernel
noncomputable def criticalQ8Slice_0 : CertifiedSlice :=
 ⟨![0,0,0,8], R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_0, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_0 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8000.positive_0 y u hy⟩
noncomputable def criticalQ8Slice_1 : CertifiedSlice :=
 ⟨![0,0,1,7], R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_1, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_1 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8000.positive_1 y u hy⟩
noncomputable def criticalQ8Slice_2 : CertifiedSlice :=
 ⟨![0,0,2,6], R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_2, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_2 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8000.positive_2 y u hy⟩
noncomputable def criticalQ8Slice_3 : CertifiedSlice :=
 ⟨![0,0,3,5], R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_3, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_3 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8000.positive_3 y u hy⟩
noncomputable def criticalQ8Slice_4 : CertifiedSlice :=
 ⟨![0,0,4,4], R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_4, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_4 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8000.positive_4 y u hy⟩
noncomputable def criticalQ8Slice_5 : CertifiedSlice :=
 ⟨![0,0,5,3], R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_5, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8000.polynomial_5 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8000.positive_5 y u hy⟩
noncomputable def criticalQ8Slice_6 : CertifiedSlice :=
 ⟨![0,0,6,2], R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_6, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_6 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8001.positive_6 y u hy⟩
noncomputable def criticalQ8Slice_7 : CertifiedSlice :=
 ⟨![0,0,7,1], R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_7, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_7 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8001.positive_7 y u hy⟩
noncomputable def criticalQ8Slice_8 : CertifiedSlice :=
 ⟨![0,0,8,0], R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_8, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_8 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8001.positive_8 y u hy⟩
noncomputable def criticalQ8Slice_9 : CertifiedSlice :=
 ⟨![0,1,0,7], R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_9, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_9 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8001.positive_9 y u hy⟩
noncomputable def criticalQ8Slice_10 : CertifiedSlice :=
 ⟨![0,1,1,6], R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_10, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_10 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8001.positive_10 y u hy⟩
noncomputable def criticalQ8Slice_11 : CertifiedSlice :=
 ⟨![0,1,2,5], R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_11, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8001.polynomial_11 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8001.positive_11 y u hy⟩
noncomputable def criticalQ8Slice_12 : CertifiedSlice :=
 ⟨![0,1,3,4], R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_12, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_12 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8002.positive_12 y u hy⟩
noncomputable def criticalQ8Slice_13 : CertifiedSlice :=
 ⟨![0,1,4,3], R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_13, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_13 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8002.positive_13 y u hy⟩
noncomputable def criticalQ8Slice_14 : CertifiedSlice :=
 ⟨![0,1,5,2], R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_14, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_14 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8002.positive_14 y u hy⟩
noncomputable def criticalQ8Slice_15 : CertifiedSlice :=
 ⟨![0,1,6,1], R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_15, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_15 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8002.positive_15 y u hy⟩
noncomputable def criticalQ8Slice_16 : CertifiedSlice :=
 ⟨![0,1,7,0], R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_16, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_16 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8002.positive_16 y u hy⟩
noncomputable def criticalQ8Slice_17 : CertifiedSlice :=
 ⟨![0,2,0,6], R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_17, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8002.polynomial_17 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8002.positive_17 y u hy⟩
noncomputable def criticalQ8Slice_18 : CertifiedSlice :=
 ⟨![0,2,1,5], R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_18, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_18 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8003.positive_18 y u hy⟩
noncomputable def criticalQ8Slice_19 : CertifiedSlice :=
 ⟨![0,2,2,4], R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_19, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_19 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8003.positive_19 y u hy⟩
noncomputable def criticalQ8Slice_20 : CertifiedSlice :=
 ⟨![0,2,3,3], R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_20, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_20 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8003.positive_20 y u hy⟩
noncomputable def criticalQ8Slice_21 : CertifiedSlice :=
 ⟨![0,2,4,2], R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_21, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_21 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8003.positive_21 y u hy⟩
noncomputable def criticalQ8Slice_22 : CertifiedSlice :=
 ⟨![0,2,5,1], R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_22, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_22 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8003.positive_22 y u hy⟩
noncomputable def criticalQ8Slice_23 : CertifiedSlice :=
 ⟨![0,2,6,0], R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_23, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8003.polynomial_23 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8003.positive_23 y u hy⟩
noncomputable def criticalQ8Slice_24 : CertifiedSlice :=
 ⟨![0,3,0,5], R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_24, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_24 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8004.positive_24 y u hy⟩
noncomputable def criticalQ8Slice_25 : CertifiedSlice :=
 ⟨![0,3,1,4], R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_25, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_25 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8004.positive_25 y u hy⟩
noncomputable def criticalQ8Slice_26 : CertifiedSlice :=
 ⟨![0,3,2,3], R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_26, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_26 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8004.positive_26 y u hy⟩
noncomputable def criticalQ8Slice_27 : CertifiedSlice :=
 ⟨![0,3,3,2], R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_27, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_27 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8004.positive_27 y u hy⟩
noncomputable def criticalQ8Slice_28 : CertifiedSlice :=
 ⟨![0,3,4,1], R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_28, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_28 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8004.positive_28 y u hy⟩
noncomputable def criticalQ8Slice_29 : CertifiedSlice :=
 ⟨![0,3,5,0], R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_29, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8004.polynomial_29 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8004.positive_29 y u hy⟩
noncomputable def criticalQ8Slice_30 : CertifiedSlice :=
 ⟨![0,4,0,4], R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_30, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_30 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8005.positive_30 y u hy⟩
noncomputable def criticalQ8Slice_31 : CertifiedSlice :=
 ⟨![0,4,1,3], R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_31, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_31 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8005.positive_31 y u hy⟩
noncomputable def criticalQ8Slice_32 : CertifiedSlice :=
 ⟨![0,4,2,2], R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_32, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_32 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8005.positive_32 y u hy⟩
noncomputable def criticalQ8Slice_33 : CertifiedSlice :=
 ⟨![0,4,3,1], R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_33, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_33 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8005.positive_33 y u hy⟩
noncomputable def criticalQ8Slice_34 : CertifiedSlice :=
 ⟨![0,4,4,0], R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_34, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_34 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8005.positive_34 y u hy⟩
noncomputable def criticalQ8Slice_35 : CertifiedSlice :=
 ⟨![0,5,0,3], R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_35, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8005.polynomial_35 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8005.positive_35 y u hy⟩
noncomputable def criticalQ8Slice_36 : CertifiedSlice :=
 ⟨![0,5,1,2], R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_36, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_36 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8006.positive_36 y u hy⟩
noncomputable def criticalQ8Slice_37 : CertifiedSlice :=
 ⟨![0,5,2,1], R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_37, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_37 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8006.positive_37 y u hy⟩
noncomputable def criticalQ8Slice_38 : CertifiedSlice :=
 ⟨![0,6,0,2], R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_38, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_38 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8006.positive_38 y u hy⟩
noncomputable def criticalQ8Slice_39 : CertifiedSlice :=
 ⟨![0,6,1,1], R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_39, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_39 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8006.positive_39 y u hy⟩
noncomputable def criticalQ8Slice_40 : CertifiedSlice :=
 ⟨![0,7,0,1], R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_40, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_40 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8006.positive_40 y u hy⟩
noncomputable def criticalQ8Slice_41 : CertifiedSlice :=
 ⟨![1,0,0,7], R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_41, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8006.polynomial_41 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8006.positive_41 y u hy⟩
noncomputable def criticalQ8Slice_42 : CertifiedSlice :=
 ⟨![1,0,1,6], R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_42, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_42 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8007.positive_42 y u hy⟩
noncomputable def criticalQ8Slice_43 : CertifiedSlice :=
 ⟨![1,0,2,5], R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_43, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_43 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8007.positive_43 y u hy⟩
noncomputable def criticalQ8Slice_44 : CertifiedSlice :=
 ⟨![1,0,3,4], R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_44, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_44 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8007.positive_44 y u hy⟩
noncomputable def criticalQ8Slice_45 : CertifiedSlice :=
 ⟨![1,0,4,3], R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_45, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_45 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8007.positive_45 y u hy⟩
noncomputable def criticalQ8Slice_46 : CertifiedSlice :=
 ⟨![1,0,5,2], R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_46, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_46 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8007.positive_46 y u hy⟩
noncomputable def criticalQ8Slice_47 : CertifiedSlice :=
 ⟨![1,0,6,1], R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_47, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8007.polynomial_47 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8007.positive_47 y u hy⟩
noncomputable def criticalQ8Slice_48 : CertifiedSlice :=
 ⟨![1,1,0,6], R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_48, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_48 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8008.positive_48 y u hy⟩
noncomputable def criticalQ8Slice_49 : CertifiedSlice :=
 ⟨![1,1,1,5], R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_49, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_49 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8008.positive_49 y u hy⟩
noncomputable def criticalQ8Slice_50 : CertifiedSlice :=
 ⟨![1,1,2,4], R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_50, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_50 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8008.positive_50 y u hy⟩
noncomputable def criticalQ8Slice_51 : CertifiedSlice :=
 ⟨![1,1,3,3], R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_51, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_51 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8008.positive_51 y u hy⟩
noncomputable def criticalQ8Slice_52 : CertifiedSlice :=
 ⟨![1,1,4,2], R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_52, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_52 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8008.positive_52 y u hy⟩
noncomputable def criticalQ8Slice_53 : CertifiedSlice :=
 ⟨![1,1,5,1], R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_53, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8008.polynomial_53 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8008.positive_53 y u hy⟩
noncomputable def criticalQ8Slice_54 : CertifiedSlice :=
 ⟨![1,2,0,5], R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_54, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_54 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8009.positive_54 y u hy⟩
noncomputable def criticalQ8Slice_55 : CertifiedSlice :=
 ⟨![1,2,1,4], R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_55, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_55 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8009.positive_55 y u hy⟩
noncomputable def criticalQ8Slice_56 : CertifiedSlice :=
 ⟨![1,2,2,3], R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_56, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_56 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8009.positive_56 y u hy⟩
noncomputable def criticalQ8Slice_57 : CertifiedSlice :=
 ⟨![1,2,3,2], R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_57, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_57 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8009.positive_57 y u hy⟩
noncomputable def criticalQ8Slice_58 : CertifiedSlice :=
 ⟨![1,2,4,1], R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_58, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_58 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8009.positive_58 y u hy⟩
noncomputable def criticalQ8Slice_59 : CertifiedSlice :=
 ⟨![1,3,0,4], R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_59, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8009.polynomial_59 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8009.positive_59 y u hy⟩
noncomputable def criticalQ8Slice_60 : CertifiedSlice :=
 ⟨![1,3,1,3], R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_60, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_60 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8010.positive_60 y u hy⟩
noncomputable def criticalQ8Slice_61 : CertifiedSlice :=
 ⟨![1,3,2,2], R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_61, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_61 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8010.positive_61 y u hy⟩
noncomputable def criticalQ8Slice_62 : CertifiedSlice :=
 ⟨![1,3,3,1], R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_62, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_62 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8010.positive_62 y u hy⟩
noncomputable def criticalQ8Slice_63 : CertifiedSlice :=
 ⟨![1,4,0,3], R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_63, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_63 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8010.positive_63 y u hy⟩
noncomputable def criticalQ8Slice_64 : CertifiedSlice :=
 ⟨![1,4,1,2], R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_64, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_64 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8010.positive_64 y u hy⟩
noncomputable def criticalQ8Slice_65 : CertifiedSlice :=
 ⟨![1,5,0,2], R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_65, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8010.polynomial_65 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8010.positive_65 y u hy⟩
noncomputable def criticalQ8Slice_66 : CertifiedSlice :=
 ⟨![2,0,0,6], R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_66, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_66 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8011.positive_66 y u hy⟩
noncomputable def criticalQ8Slice_67 : CertifiedSlice :=
 ⟨![2,0,1,5], R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_67, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_67 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8011.positive_67 y u hy⟩
noncomputable def criticalQ8Slice_68 : CertifiedSlice :=
 ⟨![2,0,2,4], R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_68, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_68 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8011.positive_68 y u hy⟩
noncomputable def criticalQ8Slice_69 : CertifiedSlice :=
 ⟨![2,0,3,3], R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_69, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_69 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8011.positive_69 y u hy⟩
noncomputable def criticalQ8Slice_70 : CertifiedSlice :=
 ⟨![2,0,4,2], R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_70, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_70 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8011.positive_70 y u hy⟩
noncomputable def criticalQ8Slice_71 : CertifiedSlice :=
 ⟨![2,1,0,5], R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_71, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8011.polynomial_71 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8011.positive_71 y u hy⟩
noncomputable def criticalQ8Slice_72 : CertifiedSlice :=
 ⟨![2,1,1,4], R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_72, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_72 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8012.positive_72 y u hy⟩
noncomputable def criticalQ8Slice_73 : CertifiedSlice :=
 ⟨![2,1,2,3], R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_73, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_73 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8012.positive_73 y u hy⟩
noncomputable def criticalQ8Slice_74 : CertifiedSlice :=
 ⟨![2,1,3,2], R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_74, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_74 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8012.positive_74 y u hy⟩
noncomputable def criticalQ8Slice_75 : CertifiedSlice :=
 ⟨![2,2,0,4], R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_75, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_75 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8012.positive_75 y u hy⟩
noncomputable def criticalQ8Slice_76 : CertifiedSlice :=
 ⟨![2,2,1,3], R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_76, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_76 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8012.positive_76 y u hy⟩
noncomputable def criticalQ8Slice_77 : CertifiedSlice :=
 ⟨![2,2,2,2], R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_77, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8012.polynomial_77 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8012.positive_77 y u hy⟩
noncomputable def criticalQ8Slice_78 : CertifiedSlice :=
 ⟨![2,3,0,3], R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_78, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_78 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8013.positive_78 y u hy⟩
noncomputable def criticalQ8Slice_79 : CertifiedSlice :=
 ⟨![3,0,0,5], R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_79, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_79 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8013.positive_79 y u hy⟩
noncomputable def criticalQ8Slice_80 : CertifiedSlice :=
 ⟨![3,0,1,4], R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_80, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_80 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8013.positive_80 y u hy⟩
noncomputable def criticalQ8Slice_81 : CertifiedSlice :=
 ⟨![3,0,2,3], R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_81, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_81 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8013.positive_81 y u hy⟩
noncomputable def criticalQ8Slice_82 : CertifiedSlice :=
 ⟨![3,1,0,4], R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_82, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_82 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8013.positive_82 y u hy⟩
noncomputable def criticalQ8Slice_83 : CertifiedSlice :=
 ⟨![3,1,1,3], R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_83, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8013.polynomial_83 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8013.positive_83 y u hy⟩
noncomputable def criticalQ8Slice_84 : CertifiedSlice :=
 ⟨![4,0,0,4], R7.Core.SpectralSliceCertificates.CriticalQ8014.polynomial_84, by
   intro u y hy
   rw [eval_eq_sum]
   change 0 < ∑ k ∈ Finset.range 9, R7.Core.Univariate.evaluate
     (R7.Core.MinorCertificates.coefficient R7.Core.SpectralSliceCertificates.CriticalQ8014.polynomial_84 k) y*u^k
   exact R7.Core.SpectralSliceCertificates.CriticalQ8014.positive_84 y u hy⟩
noncomputable def criticalQ8Certified : List CertifiedSlice := [
 criticalQ8Slice_0,
 criticalQ8Slice_1,
 criticalQ8Slice_2,
 criticalQ8Slice_3,
 criticalQ8Slice_4,
 criticalQ8Slice_5,
 criticalQ8Slice_6,
 criticalQ8Slice_7,
 criticalQ8Slice_8,
 criticalQ8Slice_9,
 criticalQ8Slice_10,
 criticalQ8Slice_11,
 criticalQ8Slice_12,
 criticalQ8Slice_13,
 criticalQ8Slice_14,
 criticalQ8Slice_15,
 criticalQ8Slice_16,
 criticalQ8Slice_17,
 criticalQ8Slice_18,
 criticalQ8Slice_19,
 criticalQ8Slice_20,
 criticalQ8Slice_21,
 criticalQ8Slice_22,
 criticalQ8Slice_23,
 criticalQ8Slice_24,
 criticalQ8Slice_25,
 criticalQ8Slice_26,
 criticalQ8Slice_27,
 criticalQ8Slice_28,
 criticalQ8Slice_29,
 criticalQ8Slice_30,
 criticalQ8Slice_31,
 criticalQ8Slice_32,
 criticalQ8Slice_33,
 criticalQ8Slice_34,
 criticalQ8Slice_35,
 criticalQ8Slice_36,
 criticalQ8Slice_37,
 CertifiedSlice.reflected ![0,5,3,0] (criticalQ8Slice_29),
 criticalQ8Slice_38,
 criticalQ8Slice_39,
 CertifiedSlice.reflected ![0,6,2,0] (criticalQ8Slice_23),
 criticalQ8Slice_40,
 CertifiedSlice.reflected ![0,7,1,0] (criticalQ8Slice_16),
 CertifiedSlice.reflected ![0,8,0,0] (criticalQ8Slice_8),
 criticalQ8Slice_41,
 criticalQ8Slice_42,
 criticalQ8Slice_43,
 criticalQ8Slice_44,
 criticalQ8Slice_45,
 criticalQ8Slice_46,
 criticalQ8Slice_47,
 CertifiedSlice.reflected ![1,0,7,0] (criticalQ8Slice_40),
 criticalQ8Slice_48,
 criticalQ8Slice_49,
 criticalQ8Slice_50,
 criticalQ8Slice_51,
 criticalQ8Slice_52,
 criticalQ8Slice_53,
 CertifiedSlice.reflected ![1,1,6,0] (criticalQ8Slice_39),
 criticalQ8Slice_54,
 criticalQ8Slice_55,
 criticalQ8Slice_56,
 criticalQ8Slice_57,
 criticalQ8Slice_58,
 CertifiedSlice.reflected ![1,2,5,0] (criticalQ8Slice_37),
 criticalQ8Slice_59,
 criticalQ8Slice_60,
 criticalQ8Slice_61,
 criticalQ8Slice_62,
 CertifiedSlice.reflected ![1,3,4,0] (criticalQ8Slice_33),
 criticalQ8Slice_63,
 criticalQ8Slice_64,
 CertifiedSlice.reflected ![1,4,2,1] (criticalQ8Slice_58),
 CertifiedSlice.reflected ![1,4,3,0] (criticalQ8Slice_28),
 criticalQ8Slice_65,
 CertifiedSlice.reflected ![1,5,1,1] (criticalQ8Slice_53),
 CertifiedSlice.reflected ![1,5,2,0] (criticalQ8Slice_22),
 CertifiedSlice.reflected ![1,6,0,1] (criticalQ8Slice_47),
 CertifiedSlice.reflected ![1,6,1,0] (criticalQ8Slice_15),
 CertifiedSlice.reflected ![1,7,0,0] (criticalQ8Slice_7),
 criticalQ8Slice_66,
 criticalQ8Slice_67,
 criticalQ8Slice_68,
 criticalQ8Slice_69,
 criticalQ8Slice_70,
 CertifiedSlice.reflected ![2,0,5,1] (criticalQ8Slice_65),
 CertifiedSlice.reflected ![2,0,6,0] (criticalQ8Slice_38),
 criticalQ8Slice_71,
 criticalQ8Slice_72,
 criticalQ8Slice_73,
 criticalQ8Slice_74,
 CertifiedSlice.reflected ![2,1,4,1] (criticalQ8Slice_64),
 CertifiedSlice.reflected ![2,1,5,0] (criticalQ8Slice_36),
 criticalQ8Slice_75,
 criticalQ8Slice_76,
 criticalQ8Slice_77,
 CertifiedSlice.reflected ![2,2,3,1] (criticalQ8Slice_61),
 CertifiedSlice.reflected ![2,2,4,0] (criticalQ8Slice_32),
 criticalQ8Slice_78,
 CertifiedSlice.reflected ![2,3,1,2] (criticalQ8Slice_74),
 CertifiedSlice.reflected ![2,3,2,1] (criticalQ8Slice_57),
 CertifiedSlice.reflected ![2,3,3,0] (criticalQ8Slice_27),
 CertifiedSlice.reflected ![2,4,0,2] (criticalQ8Slice_70),
 CertifiedSlice.reflected ![2,4,1,1] (criticalQ8Slice_52),
 CertifiedSlice.reflected ![2,4,2,0] (criticalQ8Slice_21),
 CertifiedSlice.reflected ![2,5,0,1] (criticalQ8Slice_46),
 CertifiedSlice.reflected ![2,5,1,0] (criticalQ8Slice_14),
 CertifiedSlice.reflected ![2,6,0,0] (criticalQ8Slice_6),
 criticalQ8Slice_79,
 criticalQ8Slice_80,
 criticalQ8Slice_81,
 CertifiedSlice.reflected ![3,0,3,2] (criticalQ8Slice_78),
 CertifiedSlice.reflected ![3,0,4,1] (criticalQ8Slice_63),
 CertifiedSlice.reflected ![3,0,5,0] (criticalQ8Slice_35),
 criticalQ8Slice_82,
 criticalQ8Slice_83,
 CertifiedSlice.reflected ![3,1,2,2] (criticalQ8Slice_76),
 CertifiedSlice.reflected ![3,1,3,1] (criticalQ8Slice_60),
 CertifiedSlice.reflected ![3,1,4,0] (criticalQ8Slice_31),
 CertifiedSlice.reflected ![3,2,0,3] (criticalQ8Slice_81),
 CertifiedSlice.reflected ![3,2,1,2] (criticalQ8Slice_73),
 CertifiedSlice.reflected ![3,2,2,1] (criticalQ8Slice_56),
 CertifiedSlice.reflected ![3,2,3,0] (criticalQ8Slice_26),
 CertifiedSlice.reflected ![3,3,0,2] (criticalQ8Slice_69),
 CertifiedSlice.reflected ![3,3,1,1] (criticalQ8Slice_51),
 CertifiedSlice.reflected ![3,3,2,0] (criticalQ8Slice_20),
 CertifiedSlice.reflected ![3,4,0,1] (criticalQ8Slice_45),
 CertifiedSlice.reflected ![3,4,1,0] (criticalQ8Slice_13),
 CertifiedSlice.reflected ![3,5,0,0] (criticalQ8Slice_5),
 criticalQ8Slice_84,
 CertifiedSlice.reflected ![4,0,1,3] (criticalQ8Slice_82),
 CertifiedSlice.reflected ![4,0,2,2] (criticalQ8Slice_75),
 CertifiedSlice.reflected ![4,0,3,1] (criticalQ8Slice_59),
 CertifiedSlice.reflected ![4,0,4,0] (criticalQ8Slice_30),
 CertifiedSlice.reflected ![4,1,0,3] (criticalQ8Slice_80),
 CertifiedSlice.reflected ![4,1,1,2] (criticalQ8Slice_72),
 CertifiedSlice.reflected ![4,1,2,1] (criticalQ8Slice_55),
 CertifiedSlice.reflected ![4,1,3,0] (criticalQ8Slice_25),
 CertifiedSlice.reflected ![4,2,0,2] (criticalQ8Slice_68),
 CertifiedSlice.reflected ![4,2,1,1] (criticalQ8Slice_50),
 CertifiedSlice.reflected ![4,2,2,0] (criticalQ8Slice_19),
 CertifiedSlice.reflected ![4,3,0,1] (criticalQ8Slice_44),
 CertifiedSlice.reflected ![4,3,1,0] (criticalQ8Slice_12),
 CertifiedSlice.reflected ![4,4,0,0] (criticalQ8Slice_4),
 CertifiedSlice.reflected ![5,0,0,3] (criticalQ8Slice_79),
 CertifiedSlice.reflected ![5,0,1,2] (criticalQ8Slice_71),
 CertifiedSlice.reflected ![5,0,2,1] (criticalQ8Slice_54),
 CertifiedSlice.reflected ![5,0,3,0] (criticalQ8Slice_24),
 CertifiedSlice.reflected ![5,1,0,2] (criticalQ8Slice_67),
 CertifiedSlice.reflected ![5,1,1,1] (criticalQ8Slice_49),
 CertifiedSlice.reflected ![5,1,2,0] (criticalQ8Slice_18),
 CertifiedSlice.reflected ![5,2,0,1] (criticalQ8Slice_43),
 CertifiedSlice.reflected ![5,2,1,0] (criticalQ8Slice_11),
 CertifiedSlice.reflected ![5,3,0,0] (criticalQ8Slice_3),
 CertifiedSlice.reflected ![6,0,0,2] (criticalQ8Slice_66),
 CertifiedSlice.reflected ![6,0,1,1] (criticalQ8Slice_48),
 CertifiedSlice.reflected ![6,0,2,0] (criticalQ8Slice_17),
 CertifiedSlice.reflected ![6,1,0,1] (criticalQ8Slice_42),
 CertifiedSlice.reflected ![6,1,1,0] (criticalQ8Slice_10),
 CertifiedSlice.reflected ![6,2,0,0] (criticalQ8Slice_2),
 CertifiedSlice.reflected ![7,0,0,1] (criticalQ8Slice_41),
 CertifiedSlice.reflected ![7,0,1,0] (criticalQ8Slice_9),
 CertifiedSlice.reflected ![7,1,0,0] (criticalQ8Slice_1),
 CertifiedSlice.reflected ![8,0,0,0] (criticalQ8Slice_0)
]
noncomputable def criticalQ8Groups : Groups := criticalQ8Certified.map CertifiedSlice.row
theorem criticalQ8Groups_positive (row) (hrow : row ∈ criticalQ8Groups) (u y : ℝ) (hy : 0 ≤ y) :
 0 < eval row.2 u y := certifiedRows_positive criticalQ8Certified row hrow u y hy
theorem criticalQ8Groups_short : ∀ row ∈ criticalQ8Groups, ∀ a ∈ row.2, a.length ≤ 3 := by
 decide +kernel
end R7.Core.SpectralCertificateTheorem
