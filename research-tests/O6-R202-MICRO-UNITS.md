# R202 micro-unit ledger

B14 micro-units/15 invocations, A16 micro-units/19 invocations; 30 retained declarations with immediate guarded source commits. B2-1 missed a direct Data.List.Elem import. A8-1 exposed an opaque event-position observation motive and was replaced by the honest field-input law, with actual observed-position transport subsequently proved in A9/A10. A13-1 required a second rewrite of its explicit Bool observation after unfolding the update. A16-1 lacked an explicit LBegin Action family. All four pass on attempt2. No exhaustion/reversion; B15/A17 not started; C0/ineligible.

| Unit | Attempt | Outcome | Source SHA256 | Guarded commit |
|---|---:|---|---|---|
| B1 | 1 | PASS | `e31a1f32b43aaa612626b9e752338c1f4f04508bc7da5dd75a58f98cbafe79b1` | `b94ac84eefcdcdccbf66722157a2a152929b2495` |
| B2 | 1 | REJECTED | `77cccec2878dbc054892ac03bcdf6c9db5576ea749e1762127601b41f9bd501a` | `none` |
| B2 | 2 | PASS | `e6079d35341df69dcb661bad91e82bc3230a02171ec191a832b3c76a5f11b3d9` | `27149e2b056bad6253112c88bf7946f7f0cbcc1f` |
| B3 | 1 | PASS | `97b329b2f82ed4af394bd5e145c3535e501cbd945e74f7fcdb793c14d36d3ac5` | `ec3df1863eb63b695071ae4d660d2e9a16d3beab` |
| B4 | 1 | PASS | `3fbde454381ada5878492562e18ee4cc4cd0742bce3646b2814424fc5a6a28eb` | `4ade042066d21c8beb69e5168dda9d27dd4f1492` |
| B5 | 1 | PASS | `b386dae230b26745ef673c23e70f0d4d05a1266b2c33a216a1a2fefe6193a290` | `f0859f2eca05d7d50cd5ac0ca0abd0648f1db349` |
| B6 | 1 | PASS | `0c7f62e8416d2f143d677adf16961198b9d0e7a087729beff69009007a64c39c` | `7a05198c56311ac0dc3d540200ea7957571a61b9` |
| B7 | 1 | PASS | `7bcd046b6cac1831c1149bb74f23afaceb0ff6a230eed21a9c7667eb98100ce0` | `f5acc65ffc0bc377dc8812fb22d8e1c534c30dab` |
| B8 | 1 | PASS | `8dbe1fd02bc2ffca29d877430fdd957569eb6c98bf54b2c1a922acf9ce670b8d` | `ed3b436ebf8a1b7bcb8b0d9bbd43db1f6a940602` |
| B9 | 1 | PASS | `3654df6fff15b4c2a5fd0467c7ce4780697a2dba01e9a218195d72a52e003e89` | `c0f5a286e2f920278b69a6f603c0f9013bf984b2` |
| B10 | 1 | PASS | `152882d5b7e3af6a595cf272b7509ef38589b930bc5a56194f1801ce6e2d8695` | `1be0d2029b8532c93f628ab5050c9a4eeaa93ca2` |
| B11 | 1 | PASS | `63e5cfbff8bbd7da1d0f9a294880b37da08f42fb2bebf1a3f1fb7bf100b54280` | `b357d35ee3c7270cff6ec341cf4627ac0d2b7f02` |
| B12 | 1 | PASS | `c71abd78886c0fb14e260066efc31db327dbea8803363c4c75cdbb6efa5c471d` | `186fbf450d530c2a6a25028f10a9e924065bd79e` |
| B13 | 1 | PASS | `9912e5f95b88a6d480f7b88b07e3a2ea04a9c0263a9b824cd7229bb6dd21fc30` | `e96845d44406f2842fe997e05c679fbc2c3096ac` |
| B14 | 1 | PASS | `3a5411ef263627387cc51111d27bfdfc8d957163e4b2711fc35711e3ab9105c6` | `aead55a651577fda7f2a08f4571fe5c3b9849081` |
| A1 | 1 | PASS | `b97781229a9981281b0fcd9c72c4f66a655564fc245e77de16f4ef5a35e9e63c` | `40694929357104e5e1ba1e09d0def3d584baec4a` |
| A2 | 1 | PASS | `6fd94b7c804684d0164740a31e93a816aa6da043e9809e7d04034fd7195d91ec` | `24dc4159210d141aaccdf123bdcb6aa6b4db38dd` |
| A3 | 1 | PASS | `a007c0a947554f11b4494179cb503c314bed0e9f4bc0429a61cf58912952271c` | `1588e78510f9ae305c667903f29801141e08ee5b` |
| A4 | 1 | PASS | `3ccae47ec08dbabb2c270edbea7aabed84045f29a2405ae425535a91e60a92bd` | `08182d478310d03f3dd30910f8505d21149ccfdd` |
| A5 | 1 | PASS | `7193ea08f91afad61a9d7222b7b271af8fb7631f34882e013da7de7bdf958529` | `3b482248bbafbdc0ca134c0186076b582f643c0a` |
| A6 | 1 | PASS | `c09c80856bb3f1e374b18c4bfb4d8439df1d5e9f59a3761f67018cbec5ccef41` | `d452208fac4b55e1588779929f51a947b81ce87c` |
| A7 | 1 | PASS | `b15881d96d58c07d1054725eb3e12215f5e29e22eeb54de995b5a345f3dd32ae` | `ca8523e9bfd1a9e9fbdb7a5646ea10c484c71b31` |
| A8 | 1 | REJECTED | `ecc9913ee30739e25aee9888f6177cf0b020abad78eb692f19db5813f9a6c1d9` | `none` |
| A8 | 2 | PASS | `0e363e013340ab50ddebb4fb8edbde02f929a86b8ea0702e7f43fe112ca52096` | `d8812712f2ac7b8a7faf1fae773d305236195a17` |
| A9 | 1 | PASS | `40d658265bf7529c9d2367664de3881b6eb83b5ad24b0878429bb5e2b33cabde` | `f7b030770964132bf623310aa4d841fda6e0fb3c` |
| A10 | 1 | PASS | `44b77ee0cffd54be1561bed7e12455709d8be0c938fff616205254a2ec9ca951` | `3a04acb8d5c8d6f97646164c72f3db36c7afa475` |
| A11 | 1 | PASS | `b0d31c4de7eef589a440d965e55688ff22ec46e8449be257d812f2f59117222c` | `0102b2f6a3caa9720fa1dba698896aa2a25107ef` |
| A12 | 1 | PASS | `a91d886988e67e4998590982afd27c25270723ee56e6083c794d77311757d19c` | `35e6ee23cb67f82371cee57f9caa1443913e5fd4` |
| A13 | 1 | REJECTED | `7c60c4b0565f5d8dd4c166d8aab1a61d329319fcdf34c795344ddf95c21dbbe8` | `none` |
| A13 | 2 | PASS | `566e828e0cec5191a34072204f3bff7bf60dc5281264634d37e567502eabe01f` | `650cbde32c2f35048b7e3a9a751b9c50bc775903` |
| A14 | 1 | PASS | `92f3c69aea5d2ecf8915814493b37598fa87796cf778403901e34ed3ce38efe1` | `0846ee15ebc89cd7ab9a711cf6329b6110701376` |
| A15 | 1 | PASS | `b76e2e50192b3b05970f4c5c575d6bba19fd0971ab0800299acd7311060e1eda` | `365b5cf712e92e1e3f6a76bd3665ae36cc1bed54` |
| A16 | 1 | REJECTED | `2c7d9750beaa18ff20651abd98a96f36b13a313b7c75e29026a77ef259166fee` | `none` |
| A16 | 2 | PASS | `4bf0f00b605044d590cfbf8130ee2bf8b9065d3e576f09b94529483cf5d98360` | `2a28e44e058ecf30a587c9151fc5de0bf52254c6` |

Metadata-only policy-label history: `O6-R202-POLICY-LABEL-CORRECTION.json`, with old policy bytes retained. Every source receipt is inside the raw archive; artifact publication and final-gate receipts deliberately follow its anchor.
