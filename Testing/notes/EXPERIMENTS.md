# Build experiments (claimed and run by the Haiku tenders)

Format: id / branch/commit / target / variant / measure / time limit / claimed by / result.

## id: ps3-time-1 (posted by main session)
- branch/commit: nano-parse-s3 @ 140bbc5
- target: Testing/nano/ps3/pr_a1.lean, Testing/nano/ps3/pr_a2.lean, Testing/nano/ps3/pr_a3.lean, Testing/nano/ps3/pr_a3b.lean, Testing/nano/ps3/pr_a4.lean, Testing/nano/ps3/pr_decLm.lean, Testing/nano/ps3/pr_dl.lean, Testing/nano/ps3/pr_ds.lean, Testing/nano/ps3/pr_ed.lean, Testing/nano/ps3/pr_ed2.lean, Testing/nano/ps3/pr_edM.lean, Testing/nano/ps3/pr_fd2.lean
- variant: for each file: `/usr/bin/time -f '%e s %U user %M KB' lake env lean --tstack=4000000 <file>` (after `lake build Nano`)
- measure: wall/user/RSS per file, OK/FAIL, first error lines
- time limit: 45 min per file
- claimed by: pool 2026-11-17T07:54Z

## id: ps3-time-2 (posted by main session)
- branch/commit: nano-parse-s3 @ 140bbc5
- target: Testing/nano/ps3/pr_fdM.lean, Testing/nano/ps3/pr_gs.lean, Testing/nano/ps3/pr_iw.lean, Testing/nano/ps3/pr_lookM.lean, Testing/nano/ps3/pr_moM.lean, Testing/nano/ps3/pr_nu.lean, Testing/nano/ps3/pr_rf.lean, Testing/nano/ps3/pr_sLiM.lean, Testing/nano/ps3/pr_scM.lean, Testing/nano/ps3/pr_st.lean, Testing/nano/ps3/pr_stepM.lean, Testing/nano/ps3/pr_sv.lean, Testing/nano/ps3/pr_svM.lean
- variant: for each file: `/usr/bin/time -f '%e s %U user %M KB' lake env lean --tstack=4000000 <file>` (after `lake build Nano`)
- measure: wall/user/RSS per file, OK/FAIL, first error lines
- time limit: 45 min per file
- claimed by: session_01MfKuVdPVLzxWvdAmFTdtmH (claim written by main session)

## id: ps3-profile-gs (posted by main session)
- branch/commit: nano-parse-s3 @ 140bbc5
- target: Testing/nano/ps3/pr_gs.lean (the decoder probe, 22 min 48 s last time)
- variant: `lake env lean --tstack=4000000 -Dprofiler=true -Dprofiler.threshold=200 Testing/nano/ps3/pr_gs.lean`
- measure: top 20 declarations/tactics by time; how much is s3_solve / simp / decide / kernel
- time limit: 60 min
- claimed by: session_01MfKuVaD8AUJ4tttPqcW459 (profiler; claim written by main session)

## id: ps3-profile-2b (posted by nano-parse-s3, 09:20)
- branch/commit: nano-parse-s3 @ 08b39b8
- target: Nano/ParseS3BSelf.lean (parser machine 2b, S3 compile with certificates)
- variant: `lake build Nano.ParseS3B Nano.S3Stage && lake env lean --tstack=400000 -Dprofiler=true -Dprofiler.threshold=500 Nano/ParseS3BSelf.lean 2>&1 | grep -v '^info' > prof.txt`
- measure: total wall; top 25 lines of prof.txt by time (which `cert<k>` theorems, i.e. which S3 functions: map k to the function via the `| k =>` lines of the generated φ in the info output); simp vs kernel vs elaboration
- time limit: 60 min
- claimed by:

## id: ps3-threads-2b (posted by nano-parse-s3, 09:20)
- branch/commit: nano-parse-s3 @ 08b39b8
- target: Nano/ParseS3BSelf.lean
- variant: `lake build Nano.ParseS3B Nano.S3Stage && /usr/bin/time -f '%e s %U user %M KB' lake env lean --tstack=400000 --threads=4 Nano/ParseS3BSelf.lean > /dev/null` (vs the default --threads=2 of the lakefile)
- measure: wall/user/RSS; does it finish without errors
- time limit: 60 min
- claimed by:
