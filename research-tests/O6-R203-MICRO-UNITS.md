# R203 micro-unit ledger

B16 units/21 invocations; A16 units/22 invocations.32 retained top-level declarations,32 guarded source commits.43 development checks=33 PASS+10 failures. B16-1 is a genuine PASS superseded by B16-2 explicit-index cleanup; both snapshots and the exact two-line transformation are authenticated. C0/ineligible. No exhausted/reverted unit and no budget extension.

| Unit | Attempt | Outcome | Source SHA256 | Guarded commit |
|---|---:|---|---|---|
| B1 | 1 | PASS | `7bc4218d7f5a8787a0a3cfb563c8965498946b2f1e1f5e3db38fbd7556a43456` | `df63fb6ce9ca686a15e2a48eb92257e85e68b5f6` |
| B2 | 1 | PASS | `efc7ff3349e7321ec94312db8fafa609645b2b205eb5c614e1d5b2671ff61853` | `88f4f0b048fa16ce50c71f7172dbb9627e288d51` |
| B3 | 1 | PASS | `1432c9186cd5cd25b4e5acccf1b3080695b7a164e47ca25d1d6d3bb96e77c393` | `d5c8a3e2b4583590011b28c299da107755e21697` |
| B4 | 1 | REJECTED | `275e3cd4b974251b3a72ba257d99eff887dac7b0ba0d6c7dd01278cfd879c7b3` | `none` |
| B4 | 2 | PASS | `6174f45d90115f44b5881233e3b046afe187708b38fe5075b632f8a436c6c96a` | `830a8889d1a479dbef65c8c2825f368d0b777f67` |
| B5 | 1 | PASS | `854a8d2b6a74474244158fb587667f8878c77218a370e3bb8e4aec3064761116` | `28dc44466918b6d1a73c96551a8bf5791dc10edc` |
| B6 | 1 | PASS | `147a5ef6b9cf34d073f5a0e8a463406912c65d186a492cd4915e2945b45639ee` | `ee639059e2f21dae858a2a2b7ffe7044db42432e` |
| B7 | 1 | PASS | `5a290919caf72f8eb783109116fb8e1de612683532269309a3980095acf3348a` | `c518bde1093d671301704ef9335e0c5c418d185e` |
| B8 | 1 | PASS | `9a664cbac67b37796c469250d79bb2ff5e3d98b7fa9b02d3f00269b68f1257b5` | `763e9d0bd34738f3b9d9512afb16abf25216337e` |
| B9 | 1 | REJECTED | `e2448faf6c3acac1c0488dc226245e9db964327b3ee2c87bed6e456cba8099d0` | `none` |
| B9 | 2 | PASS | `8ecce13c353217384cb014240cbea32d683abb18036bcd23dda0cac4a87cd145` | `bc17af9eddeb95adf17437db09d7f24386ab0531` |
| B10 | 1 | REJECTED | `65ff8d8a4171fd8e1720d37793d5aa98b37cb5f91e0f0beae356205bf41d6f24` | `none` |
| B10 | 2 | PASS | `c605a9c427c0b89b5e3b5edcb0534ce3506650f1928e7d588148cb5148cddc70` | `f88b8732560dab9f514b8e3c2ca8dc7b32fe1f89` |
| B11 | 1 | PASS | `5d9ebd42afb7af0fbe69b02adb495753ae31d4f48b0fe0357df2fdda6f9b712e` | `4e70974a477c611f03b27d7c31a7242fb0488f88` |
| B12 | 1 | PASS | `62dcd8b7f2e18ff9aa3fcaba09f4299dd83967ffb535e43ca20aae5cd6f7d4f7` | `66d1f47f4114b1031b97ceb4a20a989c82448d16` |
| B13 | 1 | REJECTED | `40ce584e76d54596d21f4a69c4a57a36f515b4edba74c04a69dd832d21d676cc` | `none` |
| B13 | 2 | PASS | `69aacb05336915b8ddf04e22c9d22c101452ed7d2f32a1f8b69c00e528323849` | `13be8b5714cbe95ee23979b42c9fcef4b25d3d9b` |
| B14 | 1 | PASS | `e8fd855d7a7c1df1e4ced422875c6cd0643c5ff8f0fe195eb5f81d81a40f644c` | `874513946a1e06df828ee2940f0ea2989b5fa334` |
| B15 | 1 | PASS | `a50e3ab19a5ae3def4d6347237e7f7ac22d3515bb196a5b2d58cc00a286c6794` | `36f0786a1bcb5449e2bec5ef11782f9cae082427` |
| B16 | 1 | PASS (superseded cleanup) | `f81316dc9ab123c003007525507c915280e06e95e2876a880254fb038621c71b` | `none` |
| B16 | 2 | PASS | `b92c234ef87e99fb139363183a3e841b2a171ecd7616123ae1cc270ff6c6637f` | `eb6e75a4f348f38bab306ccc625ce4c5e40cd172` |
| A1 | 1 | REJECTED | `68ab1daa1d20396df7045c306509ac9d515d27f7884781768464ea3bc858d331` | `none` |
| A1 | 2 | PASS | `c00f6168f60df39accdcf2d3ad398637bf3d68afc51a3bea1eb7f6274eb3fa33` | `8b63388369de0bf1e8f9b99d627c7ffc7db2e7ad` |
| A2 | 1 | PASS | `12efc9705e13ecaa745600ac39eae1d01c46668af83e35092008b7d0e8f8ea57` | `bc960f0a9760dfdca8633d8716cc8b166b39d1ec` |
| A3 | 1 | PASS | `25aee8c370f444279548d72ef60349203480a29372c5d553093b43f9d837bf27` | `8153cf6c96ec7c46065a2a4db5754b978c566e9d` |
| A4 | 1 | PASS | `981d7f9994c2ccce23b499a16c516d2d3edecee1173a25aa792488664f43a388` | `f376483a61119afa31ab1119018267fdf34b0f9a` |
| A5 | 1 | REJECTED | `2e2d0ee9988c3831914ef31f2c9b4937c47f078535a17264817b71193a97327b` | `none` |
| A5 | 2 | PASS | `b05d2323fbec18160bc212a7ffa3270f0e28e7dc68cfaaa24b1c181f8e410068` | `d86b7acfd4270f60c65baac8c6d0437248bb2809` |
| A6 | 1 | PASS | `bb7284dfad995a73b085b04e1ff97357a46427c21da2b68e5adf676a86fc0ae9` | `a83071a560ec397dfa78c568a453260bed38b398` |
| A7 | 1 | PASS | `8c90615d2f6f08a4da32c4dbc55e2700bdc777bcffc9a68b87e22a3c76261e86` | `3828836b169f6da623acb71c0c306434fd46a0e4` |
| A8 | 1 | REJECTED | `878059b7b6fd9e7472aa96c8ab09960f42fe58e37c4153442fa605ffe29bdcae` | `none` |
| A8 | 2 | PASS | `bfc31b767111b90228136c2e72de3f5ccbd80975d2d9fa0ce7be11772a4d8f7e` | `a0a30a8583b5f401ab3b9e0638f83ce9b1c5bada` |
| A9 | 1 | PASS | `74f3065357796d56d4e7a7e2c328dab36f95692cb89541a6133ce1e7625c1004` | `693fb232f9e5d179004e0a19a14b039d1ec789b9` |
| A10 | 1 | REJECTED | `80dc85f526af3e45f1394adfb99da112ad0dcf28b7178b9c734aebe456470126` | `none` |
| A10 | 2 | PASS | `8ea02ddda14b6644362a391be5fd032b4a2cdf9b8a87e965f78ee69ffe3a2056` | `b5e7f0061c7a689af36dc5436c77df9cfd9cf588` |
| A11 | 1 | PASS | `861971d2e32fff92916ff86763a832c08660dbbd3c02a8bd47cc5f6434a0b16d` | `5a2dab191b3f0fc7980966317145adf883619f41` |
| A12 | 1 | PASS | `ab5649d2abeeb3662ad6d1e9ecc56c91a6771b4339c5e9d3860506e09800b561` | `8f97c6c4c8eb0af662ab296a135e3e8f3f2dce28` |
| A13 | 1 | REJECTED | `5252f29399d9f59d61f1b022a068694ad7b71d457f04066e3b33b8189cfebb8f` | `none` |
| A13 | 2 | PASS | `bdb2b28c0ac4a406359f8d484d7048650036461fba7322917baaa6b760b407c1` | `6c0a23e1d3114027fb62eee20def34023aa5371e` |
| A14 | 1 | REJECTED | `a6839aed5fcc12e8023ea40d08e1030cc06f9161ad0522c9fb5838a971b3f7eb` | `none` |
| A14 | 2 | PASS | `d9759a68fbc675efdc9e0473765de35ea8bd09d190d91fb1a460f9d299fe9510` | `fcf33bb942ada8f836acbc13a55c94b3720f9cfc` |
| A15 | 1 | PASS | `9a61905597ff6df458d96b05fedf29e3f48feca193a7b12e2aa29fd980718745` | `8d78eee86f0a98dd34f445ddaf8b60715934df59` |
| A16 | 1 | PASS | `d96dea433bd8c5af7a6c648df9d62c5724b22967bac1d6bc1f6c0e1d9a430f74` | `f0c80a3707f854cb708645797c0e754a97cd33b2` |

Failure explanations and exact declaration correspondence: `O6-R203-DECLARATIONS.md`. The policy label is R203 from the first invocation; no inherited-label correction occurred. Artifact publication/final-gate receipts intentionally follow the raw archive anchor.
