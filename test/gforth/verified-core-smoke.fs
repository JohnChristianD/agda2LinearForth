\\ End-to-end smoke tests for executable conatural observations and dyad scale.

: expect-core-value ( actual expected -- )
  2dup <> IF
    ." verified core result mismatch; actual=" over . ." expected=" dup . cr
    2drop
    -4103 THROW
  ELSE
    2drop
  THEN
;

: verified-core-conat-first-observation ( -- )
  coreCoNatAtZero dethunk 1 expect-core-value
;
verified-core-conat-first-observation

: verified-core-conat-stops ( -- )
  coreCoNatStopsAtOne dethunk 0 expect-core-value
;
verified-core-conat-stops

: verified-core-infinity-observation ( -- )
  coreInfinityAtDepthEight dethunk 1 expect-core-value
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
