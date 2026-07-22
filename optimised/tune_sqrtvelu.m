load "optimised/tune_sqrtvelu_lib.m";

m_fp_256 := 135.44; s_fp_256 := 129.23; a_fp_256 := 37.99;
m_fp_512 := 338.66; s_fp_512 := 305.72; a_fp_512 := 57.79;
npts_256 := 4;
npts_512 := 2;

load "optimised/data_256.m";
Fp256 := GF(p);
Fp2_256<i256> := ExtensionField<Fp256, X | X^2 + 1>;
primes_256 := Sort(SetToSequence(SequenceToSet(
    [f[1] : f in Factorization(Ms)] cat [f[1] : f in Factorization(Mt)]
)));

printf "=== 256-bit primes (npts=%o) ===\n", npts_256;
TuneSqrtVelu(primes_256, npts_256, m_fp_256, s_fp_256, a_fp_256, Fp2_256);

load "optimised/data_512.m";
Fp512 := GF(p);
Fp2_512<i512> := ExtensionField<Fp512, X | X^2 + 1>;
primes_512 := Sort(SetToSequence(SequenceToSet(
    [f[1] : f in Factorization(Ms)]
)));

printf "\n=== 512-bit primes (npts=%o) ===\n", npts_512;
TuneSqrtVelu(primes_512, npts_512, m_fp_512, s_fp_512, a_fp_512, Fp2_512);
