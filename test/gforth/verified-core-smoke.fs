\ End-to-end smoke tests for executable functions imported from VerifiedPLLCore.

: expect-core-value ( actual expected -- )
  <> IF
    ." verified core result mismatch" cr
    -4103 THROW
  THEN
;

: verified-core-conat-first-observation ( -- )
  coreCoNatAtZero dethunk -1 expect-core-value
;
verified-core-conat-first-observation

: verified-core-conat-stops ( -- )
  coreCoNatStopsAtOne dethunk 0 expect-core-value
;
verified-core-conat-stops

: verified-core-infinity-observation ( -- )
  coreInfinityAtDepthEight dethunk -1 expect-core-value
;
verified-core-infinity-observation

: verified-core-dyad-scale-zero ( -- )
  corePow2Zero dethunk 1 expect-core-value
;
verified-core-dyad-scale-zero

: verified-core-dyad-scale-one ( -- )
  corePow2One dethunk 2 expect-core-value
;
verified-core-dyad-scale-one

." verified-core-runtime-tests-passed" cr
