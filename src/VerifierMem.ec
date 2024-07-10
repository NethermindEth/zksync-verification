require import AllCore.
require import Int.
require import IntDiv.
require import UInt256.
require import Memory.
require import PurePrimops.
require        VerifierConsts.
require        VerifierVars.

section.
import VerifierConsts VerifierVars.

declare op memory : MemoryMap.mem.

pred alpha2_mem = W256.to_uint (PurePrimops.mload memory STATE_POWER_OF_ALPHA_2_SLOT) = Alpha2.
pred alpha3_mem = W256.to_uint (PurePrimops.mload memory STATE_POWER_OF_ALPHA_3_SLOT) = Alpha3.
pred alpha4_mem = W256.to_uint (PurePrimops.mload memory STATE_POWER_OF_ALPHA_4_SLOT) = Alpha4.
pred alpha5_mem = W256.to_uint (PurePrimops.mload memory STATE_POWER_OF_ALPHA_5_SLOT) = Alpha5.
pred alpha6_mem = W256.to_uint (PurePrimops.mload memory STATE_POWER_OF_ALPHA_6_SLOT) = Alpha6.
pred alpha7_mem = W256.to_uint (PurePrimops.mload memory STATE_POWER_OF_ALPHA_7_SLOT) = Alpha7.
pred alpha8_mem = W256.to_uint (PurePrimops.mload memory STATE_POWER_OF_ALPHA_8_SLOT) = Alpha8.

pred beta_mem = W256.to_uint (PurePrimops.mload memory STATE_GAMMA_SLOT) = Gamma.
pred gamma_mem = W256.to_uint (PurePrimops.mload memory STATE_BETA_SLOT) = Beta.

pred sigma0_z_mem = W256.to_uint (PurePrimops.mload memory PROOF_COPY_PERMUTATION_POLYS_0_OPENING_AT_Z_SLOT) = Sigma0_z.
pred sigma1_z_mem = W256.to_uint (PurePrimops.mload memory PROOF_COPY_PERMUTATION_POLYS_1_OPENING_AT_Z_SLOT) = Sigma1_z.
pred sigma2_z_mem = W256.to_uint (PurePrimops.mload memory PROOF_COPY_PERMUTATION_POLYS_2_OPENING_AT_Z_SLOT) = Sigma2_z.
pred sigma3_z_mem = W256.to_uint (PurePrimops.mload memory PROOF_STATE_POLYS_3_OPENING_AT_Z_SLOT) = Sigma3_z.

pred a_z_mem = W256.to_uint (PurePrimops.mload memory PROOF_STATE_POLYS_0_OPENING_AT_Z_SLOT) = A_z.
pred b_z_mem = W256.to_uint (PurePrimops.mload memory PROOF_STATE_POLYS_1_OPENING_AT_Z_SLOT) = B_z.
pred c_z_mem = W256.to_uint (PurePrimops.mload memory PROOF_STATE_POLYS_2_OPENING_AT_Z_SLOT) = C_z.

pred zperm_zOmega_mem = W256.to_uint (PurePrimops.mload memory PROOF_COPY_PERMUTATION_GRAND_PRODUCT_OPENING_AT_Z_OMEGA_SLOT) = Zperm_zOmega.
pred l0_z_mem = W256.to_uint (PurePrimops.mload memory STATE_L_0_AT_Z_SLOT) = L0_z.

end section.
