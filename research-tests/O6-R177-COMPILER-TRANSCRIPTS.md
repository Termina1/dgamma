# R177 compiler transcripts and ledger

156 serialized compiler invocations: {'positive': 143, 'charged-proof-rejection': 12, 'authorized-check-exec-success': 1}. No engineering interrupt.

Exact UTF-8 compiler logs and original wrapper JSON/source bytes are preserved in
`O6-R177-COMPILER-EVIDENCE.tar.gz`; the JSON ledger includes raw transcripts and source hashes.
P2-4 is a qualified check+exec success, NOT an ordinary fresh-marker PASS.
Seeded package validation is NOT a cold rebuild.

## Final validation

| Check | UTC start–end | Exit | Sampled RSS KiB |
|---|---|---:|---:|
| F3-FinalCanonicalSort | 05:36:11–05:37:07 | 0 | 20152992 |
| F4-FinalUniqueCapital | 05:37:34–05:37:40 | 0 | 4624768 |
| F5-FinalFullPipeline | 05:39:31–05:41:12 | 0 | 38703008 |
| F6-FinalGeneratedStaticCoherence | 05:44:16–05:44:21 | 0 | 3513568 |
| F7-SeededPackage207 | 05:44:29–05:44:45 | 0 | 224144 |

## All invocations

| Unit | Classification | UTC start–end | Exit | Building marker | Commit |
|---|---|---|---:|---|---|
| A1-1 | positive | 02:43:38–02:43:39 | 0 | True | 9c2d960 |
| A2-1 | positive | 02:43:54–02:43:55 | 0 | True | 5c372c2 |
| A3-1 | positive | 02:45:11–02:45:12 | 0 | True | 4c933c9 |
| A4-1 | positive | 02:45:12–02:45:13 | 0 | True | 4760c12 |
| A5-1 | positive | 02:45:26–02:45:27 | 0 | True | fa8bd9d |
| A6-1 | positive | 02:45:55–02:46:51 | 0 | True | 225605e |
| A7-1 | positive | 02:47:41–02:48:37 | 0 | True | e54afaf |
| A8-1 | positive | 02:49:09–02:50:05 | 0 | True | f438310 |
| A9-1 | positive | 02:50:37–02:50:38 | 0 | True | 3ef0d0a |
| A10-1 | positive | 02:50:38–02:50:39 | 0 | True | 7eedd31 |
| A11-1 | positive | 02:51:14–02:52:10 | 0 | True | 58e21ed |
| A12-1 | positive | 02:54:28–02:55:24 | 0 | True | 2beb816 |
| B1-1 | positive | 02:57:39–02:57:40 | 0 | True |  |
| C1-1 | positive | 02:58:54–02:58:55 | 0 | True |  |
| F1-CanonicalSort | positive | 03:00:00–03:00:56 | 0 | True |  |
| F2-UniqueCapital | positive | 03:01:12–03:01:23 | 0 | True |  |
| B2-1 | positive | 03:05:45–03:05:46 | 0 | True | 3d95e6b |
| B3-1 | positive | 03:06:05–03:06:06 | 0 | True | 8049213 |
| B4-1 | positive | 03:06:31–03:06:32 | 0 | True | ed0f2af |
| B5-1 | charged-proof-rejection | 03:06:49–03:06:51 | 1 | True | 298dfa0 |
| B5-2 | positive | 03:07:14–03:07:15 | 0 | True | 298dfa0 |
| B6-1 | positive | 03:07:30–03:07:31 | 0 | True | de38fd4 |
| B7-1 | positive | 03:07:55–03:07:56 | 0 | True | 892a156 |
| B8-1 | positive | 03:08:39–03:08:40 | 0 | True | c1dcb5c |
| B9-1 | positive | 03:08:52–03:08:53 | 0 | True | 0d7249f |
| B10-1 | positive | 03:10:00–03:10:01 | 0 | True | 88ec564 |
| B11-1 | positive | 03:10:20–03:10:21 | 0 | True | ae0e4dd |
| B12-1 | positive | 03:11:29–03:11:37 | 0 | True | d0826f8 |
| B13-1 | positive | 03:12:19–03:12:27 | 0 | True | f8471a8 |
| B14-1 | positive | 03:13:07–03:13:15 | 0 | True | 1bb4208 |
| B15-1 | positive | 03:14:17–03:14:25 | 0 | True | dcf2a0b |
| B16-1 | positive | 03:14:51–03:14:59 | 0 | True | 8029a3b |
| B17-1 | positive | 03:15:54–03:16:02 | 0 | True | 0a03fd9 |
| B18-1 | charged-proof-rejection | 03:16:52–03:16:55 | 1 | True | fa14e14 |
| B18-2 | positive | 03:17:17–03:17:18 | 0 | True | fa14e14 |
| B19-1 | positive | 03:17:33–03:17:34 | 0 | True | 0af908d |
| B20-1 | positive | 03:18:03–03:18:11 | 0 | True | 402c09d |
| B21-1 | positive | 03:18:57–03:19:05 | 0 | True | f91f2ca |
| B22-1 | positive | 03:23:07–03:23:08 | 0 | True | 5964850 |
| B23-1 | positive | 03:23:36–03:23:37 | 0 | True | 4c0541f |
| B24-1 | positive | 03:24:31–03:24:32 | 0 | True | 6b944ee |
| B25-1 | positive | 03:25:01–03:25:03 | 0 | True | 07a6e63 |
| B26-1 | positive | 03:25:31–03:25:33 | 0 | True | dd55c0f |
| B27-1 | positive | 03:26:03–03:26:05 | 0 | True | b28637f |
| B28-1 | positive | 03:26:30–03:26:38 | 0 | True | 19807ca |
| B29-1 | positive | 03:27:46–03:27:54 | 0 | True | f26fe5f |
| B30-1 | positive | 03:32:20–03:32:22 | 0 | True | c1730f1 |
| B31-1 | positive | 03:32:40–03:32:42 | 0 | True | f939661 |
| B32-1 | positive | 03:33:00–03:33:02 | 0 | True | b117bda |
| B33-1 | positive | 03:33:20–03:33:22 | 0 | True | c21abfb |
| B34-1 | positive | 03:33:37–03:33:39 | 0 | True | 7815c8b |
| B35-1 | charged-proof-rejection | 03:34:17–03:34:18 | 1 | True | 3aed56f |
| B35-2 | positive | 03:35:07–03:35:09 | 0 | True | 3aed56f |
| B36-1 | charged-proof-rejection | 03:35:59–03:36:00 | 1 | True | 38f4e42 |
| B36-2 | positive | 03:36:29–03:36:31 | 0 | True | 38f4e42 |
| B37-1 | positive | 03:37:06–03:37:08 | 0 | True | 44bc43e |
| B38-1 | positive | 03:37:32–03:37:34 | 0 | True | 03cde7b |
| B39-1 | positive | 03:37:57–03:37:59 | 0 | True | 2e1f36b |
| B40-1 | charged-proof-rejection | 03:38:52–03:38:54 | 1 | True | 5e25a18 |
| B40-2 | positive | 03:39:13–03:39:16 | 0 | True | 5e25a18 |
| B41-1 | positive | 03:39:41–03:39:44 | 0 | True | a0be307 |
| B42-1 | positive | 03:40:43–03:40:45 | 0 | True | f7fc3b3 |
| B43-1 | charged-proof-rejection | 03:41:11–03:41:13 | 1 | True | b1e0f83 |
| B43-2 | positive | 03:41:32–03:41:34 | 0 | True | b1e0f83 |
| B44-1 | positive | 03:42:08–03:42:10 | 0 | True | 046fef9 |
| B45-1 | positive | 03:42:41–03:42:43 | 0 | True | 41cc8f5 |
| B46-1 | positive | 03:43:12–03:43:14 | 0 | True | 8b52d9d |
| B47-1 | positive | 03:43:38–03:43:40 | 0 | True | 273affc |
| B48-1 | positive | 03:44:04–03:44:06 | 0 | True | 2523e49 |
| B49-1 | positive | 03:44:31–03:44:40 | 0 | True | 37018db |
| B50-1 | positive | 03:45:17–03:45:25 | 0 | True | 13c26a6 |
| B51-1 | positive | 03:46:14–03:46:16 | 0 | True | ee2bc29 |
| B52-1 | positive | 03:46:38–03:46:40 | 0 | True | 2bf5649 |
| B53-1 | positive | 03:47:34–03:47:42 | 0 | True | bdb9d90 |
| B54-1 | positive | 03:48:58–03:49:07 | 0 | True | f1edca1 |
| P1-1 | positive | 03:53:21–03:54:10 | 0 | True | e2f967b |
| P2-1 | charged-proof-rejection | 03:55:30–03:55:31 | 1 | True |  |
| P2-2 | charged-proof-rejection | 03:59:12–03:59:14 | 1 | True |  |
| P2-3 | charged-proof-rejection | 04:02:02–04:02:04 | 1 | True |  |
| P2-4 | authorized-check-exec-success | 04:09:54–04:09:57 | 0 | False | a5b5364 |
| B55-1 | positive | 04:13:21–04:13:22 | 0 | True | 118de6b |
| B56-1 | positive | 04:14:13–04:14:14 | 0 | True | b5d86a0 |
| B57-1 | positive | 04:14:39–04:14:40 | 0 | True | 3860950 |
| B58-1 | positive | 04:15:08–04:15:09 | 0 | True | 19a89bd |
| B59-1 | positive | 04:16:12–04:16:13 | 0 | True | 6989130 |
| B60-1 | positive | 04:16:53–04:16:54 | 0 | True | ecaee1a |
| B61-1 | positive | 04:17:47–04:17:48 | 0 | True | 04ea7a8 |
| B62-1 | positive | 04:18:26–04:18:28 | 0 | True | ca7bba8 |
| B63-1 | positive | 04:18:49–04:18:51 | 0 | True | 91a1074 |
| B64-1 | positive | 04:22:30–04:22:32 | 0 | True | 7466612 |
| B65-1 | positive | 04:22:58–04:23:00 | 0 | True | a0bc4ab |
| B66-1 | positive | 04:23:33–04:23:35 | 0 | True | d74b93e |
| B67-1 | positive | 04:24:32–04:24:41 | 0 | True | 2e089ea |
| B68-1 | positive | 04:26:52–04:26:54 | 0 | True | c074557 |
| B69-1 | positive | 04:27:20–04:27:28 | 0 | True | 03e1dfe |
| B70-1 | positive | 04:27:54–04:28:03 | 0 | True | 3ffe36d |
| B71-1 | positive | 04:28:22–04:28:31 | 0 | True | 8bfc631 |
| B72-1 | positive | 04:29:12–04:29:21 | 0 | True | 5b9aca6 |
| B73-1 | positive | 04:30:17–04:30:26 | 0 | True | 7ac9a03 |
| B74-1 | positive | 04:33:03–04:33:05 | 0 | True | bd40fbb |
| B75-1 | positive | 04:34:05–04:34:07 | 0 | True | 5c608cf |
| B76-1 | positive | 04:35:25–04:35:27 | 0 | True | a70d85a |
| B77-1 | positive | 04:36:19–04:36:21 | 0 | True | 6193510 |
| B78-1 | positive | 04:37:29–04:37:32 | 0 | True | 18fd21b |
| B79-1 | positive | 04:39:10–04:39:12 | 0 | True | c9ddb2d |
| B80-1 | positive | 04:40:34–04:40:36 | 0 | True | fadd8d2 |
| B81-1 | charged-proof-rejection | 04:41:46–04:41:53 | 1 | True | b65fc6d |
| B81-2 | positive | 04:42:36–04:42:39 | 0 | True | b65fc6d |
| B82-1 | positive | 04:43:40–04:43:43 | 0 | True | 3a40e18 |
| B83-1 | positive | 04:44:59–04:45:02 | 0 | True | 87a814e |
| B84-1 | positive | 04:45:23–04:45:26 | 0 | True | 6bc501d |
| B85-1 | positive | 04:52:30–04:52:32 | 0 | True | 2bae112 |
| B86-1 | positive | 04:53:19–04:53:21 | 0 | True | 980d417 |
| B87-1 | positive | 04:53:55–04:53:56 | 0 | True | 9b600af |
| B88-1 | positive | 04:54:23–04:54:24 | 0 | True | 085fc33 |
| B89-1 | positive | 04:54:49–04:54:50 | 0 | True | cc933d0 |
| B90-1 | positive | 04:55:24–04:55:25 | 0 | True | 35ca03e |
| B91-1 | positive | 04:56:04–04:56:05 | 0 | True | 6f92486 |
| B92-1 | positive | 04:56:33–04:56:34 | 0 | True | 5de557f |
| B93-1 | positive | 04:56:51–04:56:52 | 0 | True | 7ef0c04 |
| B94-1 | positive | 04:57:50–04:57:51 | 0 | True | a46c421 |
| B95-1 | charged-proof-rejection | 04:58:16–04:58:17 | 1 | True | bf468a5 |
| B95-2 | positive | 04:58:32–04:58:33 | 0 | True | bf468a5 |
| B96-1 | positive | 04:58:54–04:58:55 | 0 | True | 2e3a0aa |
| B97-1 | positive | 04:59:44–04:59:45 | 0 | True | 5031feb |
| B98-1 | positive | 05:00:47–05:00:48 | 0 | True | 763fb34 |
| B99-1 | positive | 05:03:03–05:03:04 | 0 | True | 69d5a25 |
| B100-1 | positive | 05:03:30–05:03:31 | 0 | True | e47338c |
| B101-1 | positive | 05:06:55–05:06:59 | 0 | True | 1a01db2 |
| B102-1 | charged-proof-rejection | 05:08:51–05:08:59 | 1 | True | dc53176 |
| B102-2 | positive | 05:09:19–05:09:28 | 0 | True | dc53176 |
| B103-1 | positive | 05:10:16–05:10:26 | 0 | True | dd637b3 |
| B104-1 | positive | 05:11:14–05:11:23 | 0 | True | 1a86c79 |
| B105-1 | positive | 05:11:48–05:11:58 | 0 | True | 796c5fe |
| B106-1 | positive | 05:12:31–05:12:40 | 0 | True | 01f8226 |
| B107-1 | positive | 05:13:00–05:13:10 | 0 | True | 139ee3e |
| B108-1 | positive | 05:14:47–05:14:50 | 0 | True | 36c52b3 |
| B109-1 | positive | 05:15:30–05:15:33 | 0 | True | 594ed11 |
| B110-1 | positive | 05:16:27–05:16:30 | 0 | True | 69ffdfb |
| B111-1 | positive | 05:20:24–05:20:27 | 0 | True | bc83710 |
| B112-1 | positive | 05:21:32–05:21:34 | 0 | True | e28cc2a |
| B113-1 | positive | 05:22:07–05:22:10 | 0 | True | eaee922 |
| B114-1 | positive | 05:22:48–05:22:50 | 0 | True | de2d451 |
| B115-1 | positive | 05:25:19–05:25:21 | 0 | True | 0e215a0 |
| B116-1 | positive | 05:26:20–05:26:22 | 0 | True | 9c00454 |
| B117-1 | positive | 05:27:37–05:27:47 | 0 | True | ccda19a |
| B118-1 | positive | 05:28:49–05:28:52 | 0 | True | 6480d14 |
| B119-1 | positive | 05:30:43–05:30:47 | 0 | True | 3aa5cb6 |
| B120-1 | positive | 05:31:15–05:31:19 | 0 | True | bb92f41 |
| B121-1 | positive | 05:32:39–05:32:43 | 0 | True | da6beec |
| B122-1 | positive | 05:33:19–05:33:23 | 0 | True | 62dede6 |
| F3-FinalCanonicalSort | positive | 05:36:11–05:37:07 | 0 | True |  |
| F4-FinalUniqueCapital | positive | 05:37:34–05:37:40 | 0 | True |  |
| F5-FinalFullPipeline | positive | 05:39:31–05:41:12 | 0 | True |  |
| F6-FinalGeneratedStaticCoherence | positive | 05:44:16–05:44:21 | 0 | True |  |
| F7-SeededPackage207 | positive | 05:44:29–05:44:45 | 0 | n/a (seeded) |  |

## A1-1 — positive

```text
START 2026-09-07T02:43:38.740477+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)
END 2026-09-07T02:43:39.791321+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## A2-1 — positive

```text
START 2026-09-07T02:43:54.435049+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)
END 2026-09-07T02:43:55.487532+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## A3-1 — positive

```text
START 2026-09-07T02:45:11.433269+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)
END 2026-09-07T02:45:12.476164+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## A4-1 — positive

```text
START 2026-09-07T02:45:12.575765+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)
END 2026-09-07T02:45:13.611052+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## A5-1 — positive

```text
START 2026-09-07T02:45:26.212434+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)
END 2026-09-07T02:45:27.252725+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## A6-1 — positive

```text
START 2026-09-07T02:45:55.176348+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted
END 2026-09-07T02:46:51.076305+00:00 exit=0 fresh=True sampledRSSKiB=20113536
```

## A7-1 — positive

```text
START 2026-09-07T02:47:41.642164+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted
END 2026-09-07T02:48:37.587678+00:00 exit=0 fresh=True sampledRSSKiB=20141424
```

## A8-1 — positive

```text
START 2026-09-07T02:49:09.392100+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted
END 2026-09-07T02:50:05.353674+00:00 exit=0 fresh=True sampledRSSKiB=20131920
```

## A9-1 — positive

```text
START 2026-09-07T02:50:37.323961+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)
END 2026-09-07T02:50:38.386129+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## A10-1 — positive

```text
START 2026-09-07T02:50:38.477239+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceWorkMeasureSpike.idr
1/1: Building DGamma.CP5ConfluenceWorkMeasureSpike (research/DGamma/CP5ConfluenceWorkMeasureSpike.idr)
END 2026-09-07T02:50:39.534304+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## A11-1 — positive

```text
START 2026-09-07T02:51:14.309200+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted
END 2026-09-07T02:52:10.304202+00:00 exit=0 fresh=True sampledRSSKiB=19550464
```

## A12-1 — positive

```text
START 2026-09-07T02:54:28.723896+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted
END 2026-09-07T02:55:24.647163+00:00 exit=0 fresh=True sampledRSSKiB=20142624
```

## B1-1 — positive

```text
START 2026-09-07T02:57:39.722231+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R177ExactCurrentDomainProbe.idr
1/1: Building DGamma.R177ExactCurrentDomainProbe (research-tests/DGamma/R177ExactCurrentDomainProbe.idr)
END 2026-09-07T02:57:40.765369+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## C1-1 — positive

```text
START 2026-09-07T02:58:54.673648+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R177AuthenticatedCurrentBirthProbe.idr
1/1: Building DGamma.R177AuthenticatedCurrentBirthProbe (research-tests/DGamma/R177AuthenticatedCurrentBirthProbe.idr)
END 2026-09-07T02:58:55.729245+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## F1-CanonicalSort — positive

```text
START 2026-09-07T03:00:00.555751+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted
END 2026-09-07T03:00:56.524372+00:00 exit=0 fresh=True sampledRSSKiB=20152800
```

## F2-UniqueCapital — positive

```text
START 2026-09-07T03:01:12.576123+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr
 9/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
10/12: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 |
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:736:3--742:55
 736 |   OperationalActorDone :
 737 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 738 |       order trace) ->
 739 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 740 |       keyEq trace) ->
 741 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:743:3--759:35
 743 |   OperationalActorStep :
 744 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 745 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 746 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 747 |       before sourceTrace) ->
 748 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1219:3--1227:41
 1219 | 0 permutationReplayCorrespondence :
 1220 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1221 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1222 |       rightCapital matching} ->
 1223 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1224 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1233:3--1241:41
 1233 | 0 permutationOccurrenceCorrespondence :
 1234 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1235 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1236 |       rightCapital matching} ->
 1237 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1238 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

12/12: Building DGamma.CP5UniqueRawNameCanonicalCapital (research/DGamma/CP5UniqueRawNameCanonicalCapital.idr)
END 2026-09-07T03:01:23.972532+00:00 exit=0 fresh=True sampledRSSKiB=1957472
```

## B2-1 — positive

```text
START 2026-09-07T03:05:45.336361+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:05:46.374834+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B3-1 — positive

```text
START 2026-09-07T03:06:05.054193+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:06:06.105058+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B4-1 — positive

```text
START 2026-09-07T03:06:31.031412+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:06:32.076201+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B5-1 — charged-proof-rejection

```text
START 2026-09-07T03:06:49.997494+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
Error: While processing left hand side of currentPutEntryOrigin. When unifying:
    [(?selected, ?generation)]
and:
    [(?inserted, ?fresh)]
Pattern variable fresh unifies with: ?generation [no locals in scope].

DGamma.CP5CurrentGenerationBirthSpike:81:44--81:72
    |
 81 | currentPutEntryOrigin name nameEq inserted fresh [] selected generation Here = Left Refl
    |                                            ^^^^^             ^^^^^^^^^^

Suggestion: Use the same name for both pattern variables, since they unify.
END 2026-09-07T03:06:51.045806+00:00 exit=1 fresh=True sampledRSSKiB=0
```

## B5-2 — positive

```text
START 2026-09-07T03:07:14.301574+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:07:15.334596+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B6-1 — positive

```text
START 2026-09-07T03:07:30.330385+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:07:31.368298+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B7-1 — positive

```text
START 2026-09-07T03:07:55.207320+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:07:56.240985+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B8-1 — positive

```text
START 2026-09-07T03:08:39.249423+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:08:40.287909+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B9-1 — positive

```text
START 2026-09-07T03:08:52.396942+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:08:53.435431+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B10-1 — positive

```text
START 2026-09-07T03:10:00.899743+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:10:01.936872+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B11-1 — positive

```text
START 2026-09-07T03:10:20.043383+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:10:21.081353+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B12-1 — positive

```text
START 2026-09-07T03:11:29.317196+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:11:37.597668+00:00 exit=0 fresh=True sampledRSSKiB=2938928
```

## B13-1 — positive

```text
START 2026-09-07T03:12:19.380720+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:12:27.669939+00:00 exit=0 fresh=True sampledRSSKiB=2931824
```

## B14-1 — positive

```text
START 2026-09-07T03:13:07.688030+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:13:15.995331+00:00 exit=0 fresh=True sampledRSSKiB=2935904
```

## B15-1 — positive

```text
START 2026-09-07T03:14:17.176609+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:14:25.489567+00:00 exit=0 fresh=True sampledRSSKiB=2932928
```

## B16-1 — positive

```text
START 2026-09-07T03:14:51.502176+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:14:59.796186+00:00 exit=0 fresh=True sampledRSSKiB=2937664
```

## B17-1 — positive

```text
START 2026-09-07T03:15:54.655444+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:16:02.945802+00:00 exit=0 fresh=True sampledRSSKiB=2940048
```

## B18-1 — charged-proof-rejection

```text
START 2026-09-07T03:16:52.913149+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
Error: While processing type of currentBirthAtPrefixComponent. Undefined name AlignedTransitions.

DGamma.CP5CurrentGenerationBirthSpike:212:3--212:21
 208 |   {initial, middle, finalState : SystemState name key value world error} ->
 209 |   (global : Transitions initial finalState) ->
 210 |   (prior : Transitions initial middle) -> (later : Transitions middle finalState) ->
 211 |   (appendTransitions prior later = global) ->
 212 |   AlignedTransitions name key world error value nameEq keyEq prior ->
         ^^^^^^^^^^^^^^^^^^
Did you mean any of: appendTransitions, MoreTransitions, checkedTransition, or locatedTransition?
Error: No type declaration for DGamma.CP5CurrentGenerationBirthSpike.currentBirthAtPrefixComponent.

DGamma.CP5CurrentGenerationBirthSpike:223:1--230:132
 223 | currentBirthAtPrefixComponent name key world error value nameEq keyEq global prior later decomposition aligned empty unique
 224 |   selected generation authentication observed found =
 225 |     case authentication of
 226 |       MkCurrentGenerationBirth scanParent scanComponent scanBirth exact =>
 227 |         case rawComponentBirthAtPrefix name key world error value nameEq keyEq global prior later decomposition aligned empty selected observed found of
 228 |           (parent ** birth) => (parent ** birth ** trans exact
Did you mean: currentBirthComponent?
END 2026-09-07T03:16:55.009498+00:00 exit=1 fresh=True sampledRSSKiB=232720
```

## B18-2 — positive

```text
START 2026-09-07T03:17:17.043386+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:17:18.076953+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B19-1 — positive

```text
START 2026-09-07T03:17:33.512346+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:17:34.552550+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B20-1 — positive

```text
START 2026-09-07T03:18:03.041862+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:18:11.344450+00:00 exit=0 fresh=True sampledRSSKiB=2943760
```

## B21-1 — positive

```text
START 2026-09-07T03:18:57.637668+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:19:05.927260+00:00 exit=0 fresh=True sampledRSSKiB=3974480
```

## B22-1 — positive

```text
START 2026-09-07T03:23:07.820824+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:23:08.853191+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B23-1 — positive

```text
START 2026-09-07T03:23:36.350399+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:23:37.387883+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B24-1 — positive

```text
START 2026-09-07T03:24:31.041009+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:24:32.084316+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B25-1 — positive

```text
START 2026-09-07T03:25:01.475121+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:25:03.569698+00:00 exit=0 fresh=True sampledRSSKiB=240704
```

## B26-1 — positive

```text
START 2026-09-07T03:25:31.902166+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:25:33.992828+00:00 exit=0 fresh=True sampledRSSKiB=283136
```

## B27-1 — positive

```text
START 2026-09-07T03:26:03.786082+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:26:05.856604+00:00 exit=0 fresh=True sampledRSSKiB=233904
```

## B28-1 — positive

```text
START 2026-09-07T03:26:30.226885+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:26:38.521200+00:00 exit=0 fresh=True sampledRSSKiB=4550080
```

## B29-1 — positive

```text
START 2026-09-07T03:27:46.360581+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:27:54.669779+00:00 exit=0 fresh=True sampledRSSKiB=4501648
```

## B30-1 — positive

```text
START 2026-09-07T03:32:20.788304+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:32:22.877362+00:00 exit=0 fresh=True sampledRSSKiB=207968
```

## B31-1 — positive

```text
START 2026-09-07T03:32:40.912917+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:32:42.997877+00:00 exit=0 fresh=True sampledRSSKiB=232496
```

## B32-1 — positive

```text
START 2026-09-07T03:33:00.736512+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:33:02.812701+00:00 exit=0 fresh=True sampledRSSKiB=228624
```

## B33-1 — positive

```text
START 2026-09-07T03:33:20.321898+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:33:22.400145+00:00 exit=0 fresh=True sampledRSSKiB=230560
```

## B34-1 — positive

```text
START 2026-09-07T03:33:37.359168+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:33:39.444243+00:00 exit=0 fresh=True sampledRSSKiB=214880
```

## B35-1 — charged-proof-rejection

```text
START 2026-09-07T03:34:17.146154+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
Error: While processing right hand side of currentBeginOwner. Can't solve constraint between: case targetFiber (MkFiber component parent retiredFlag table (Inactive Nothing)) (registry before) of
  { Nothing => Nothing
  ; Just item => (\view => Just (LBeginTag, MkSystemState (worldState before) (replaceBinding actor (setFiberLifecycle (MkFiber component parent retiredFlag table (Inactive Nothing)) (Reloading (componentProgram component) id view)) (registry before)))) item
  } and case targetFiber (MkFiber component parent retiredFlag table (Inactive Nothing)) (registry before) of
  { Nothing => Nothing
  ; Just view => Just (LBeginTag, MkSystemState (worldState before) (replaceBinding actor (setFiberLifecycle (MkFiber component parent retiredFlag table (Inactive Nothing)) (Reloading (componentProgram (fiberComponent (MkFiber component parent retiredFlag table (Inactive Nothing)))) id view)) (registry before)))
  }.

DGamma.CP5CurrentGenerationBirthSpike:468:22--477:45
 468 |     rewrite found in currentResultOwnerMaybe name key world error value nameEq actor
 469 |       (View name (dependencies (componentDependencies component)))
 470 |       (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Inactive Nothing)) (registry before))
 471 |       (\view => Just (LBeginTag, MkSystemState (worldState before)
 472 |         (replaceBinding @{nameEq} actor (setFiberLifecycle (MkFiber component parent retiredFlag table (Inactive Nothing))
 473 |           (Reloading (componentProgram component) id view)) (registry before))))
END 2026-09-07T03:34:18.180897+00:00 exit=1 fresh=True sampledRSSKiB=0
```

## B35-2 — positive

```text
START 2026-09-07T03:35:07.193107+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:35:09.276566+00:00 exit=0 fresh=True sampledRSSKiB=204368
```

## B36-1 — charged-proof-rejection

```text
START 2026-09-07T03:35:59.586590+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
Error: While processing right hand side of currentDivertOwner. Can't solve constraint between: if targetMatches (targetFiber (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (registry before)) view then Nothing else Just (LDivertTag, MkSystemState (worldState before) (replaceBinding actor (setFiberLifecycle (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (Unloading accumulator view Nothing)) (registry before))) and if targetMatches (targetFiber (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (registry before)) view then Nothing else Just (LDivertTag, MkSystemState (worldState before) (replaceBinding actor (setFiberLifecycle (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (Unloading accumulator view Nothing)) (registry before))).

DGamma.CP5CurrentGenerationBirthSpike:498:22--505:46
 498 |     rewrite found in currentResultOwnerIf name key world error value nameEq actor
 499 |       (targetMatches @{nameEq} (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (registry before)) view)
 500 |       Nothing (Just (LDivertTag, MkSystemState (worldState before) (replaceBinding @{nameEq} actor
 501 |         (setFiberLifecycle (MkFiber component parent retiredFlag table (Reloading remaining accumulator view)) (Unloading accumulator view Nothing)) (registry before))))
 502 |       () (currentResultOwnerReplace name key world error value nameEq actor (registry before)
 503 |         (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))
END 2026-09-07T03:36:00.623138+00:00 exit=1 fresh=True sampledRSSKiB=0
```

## B36-2 — positive

```text
START 2026-09-07T03:36:29.484518+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:36:31.563022+00:00 exit=0 fresh=True sampledRSSKiB=246304
```

## B37-1 — positive

```text
START 2026-09-07T03:37:06.869347+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:37:08.948496+00:00 exit=0 fresh=True sampledRSSKiB=248624
```

## B38-1 — positive

```text
START 2026-09-07T03:37:32.494959+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:37:34.571438+00:00 exit=0 fresh=True sampledRSSKiB=240288
```

## B39-1 — positive

```text
START 2026-09-07T03:37:57.765756+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:37:59.866875+00:00 exit=0 fresh=True sampledRSSKiB=254656
```

## B40-1 — charged-proof-rejection

```text
START 2026-09-07T03:38:52.162488+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
Error: While processing type of currentAdvanceOutcomeOwner. Can't solve constraint between: ?world [no locals in scope] and world.

DGamma.CP5CurrentGenerationBirthSpike:589:101--589:116
 585 |   (view : View name (dependencies (componentDependencies component))) ->
 586 |   (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry before) =
 587 |     Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))) ->
 588 |   (capability : DepValues key value (dependencies (componentDependencies component))) ->
 589 |   (resolveCommittedValues @{nameEq} @{keyEq} (dependencies (componentDependencies component)) view (registry before) = Just capability) ->
                                                                                                           ^^^^^^^^^^^^^^^

Error: No type declaration for DGamma.CP5CurrentGenerationBirthSpike.currentAdvanceOutcomeOwner.

DGamma.CP5CurrentGenerationBirthSpike:596:1--600:40
 596 | currentAdvanceOutcomeOwner name key world error value nameEq keyEq actor before component parent retiredFlag table step rest accumulator view found capability resolved (Left failure) ran condition exact =
 597 |   rewrite found in rewrite resolved in rewrite ran in currentResultOwnerReplace name key world error value nameEq actor (registry before)
 598 |     (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))
 599 |     (setFiberLifecycle (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) (Unloading accumulator view (Just failure)))
 600 |     found (worldState before) LRaiseTag
Did you mean: currentAdvanceEmptyOwner?
END 2026-09-07T03:38:54.227474+00:00 exit=1 fresh=True sampledRSSKiB=243856
```

## B40-2 — positive

```text
START 2026-09-07T03:39:13.903663+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:39:16.002000+00:00 exit=0 fresh=True sampledRSSKiB=235040
```

## B41-1 — positive

```text
START 2026-09-07T03:39:41.986433+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:39:44.086624+00:00 exit=0 fresh=True sampledRSSKiB=241616
```

## B42-1 — positive

```text
START 2026-09-07T03:40:43.657280+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:40:45.741196+00:00 exit=0 fresh=True sampledRSSKiB=237760
```

## B43-1 — charged-proof-rejection

```text
START 2026-09-07T03:41:11.716960+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
Error: While processing right hand side of currentLifecycleTargetPresent. let 0 lifecycle = ?postpone in ($resolved23637) tag key value error world name afterState before action keyEq nameEq raw ?postpone parent component same is not a valid impossible case.

DGamma.CP5CurrentGenerationBirthSpike:712:73--712:88
 708 |     lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
 709 |       @{nameEq} (actionOwner action) (registry afterState) = Just fiber)
 710 | currentLifecycleTargetPresent name key world error value nameEq keyEq action lifecycle before afterState tag raw =
 711 |   case currentOwnerSourceObserved name key world error value nameEq keyEq action before afterState tag raw
 712 |     (\parent, component, same => case same of Refl => case lifecycle of Refl impossible)
                                                                               ^^^^^^^^^^^^^^^
END 2026-09-07T03:41:13.791360+00:00 exit=1 fresh=True sampledRSSKiB=233664
```

## B43-2 — positive

```text
START 2026-09-07T03:41:32.582071+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:41:34.670661+00:00 exit=0 fresh=True sampledRSSKiB=233072
```

## B44-1 — positive

```text
START 2026-09-07T03:42:08.424198+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:42:10.504184+00:00 exit=0 fresh=True sampledRSSKiB=235264
```

## B45-1 — positive

```text
START 2026-09-07T03:42:41.869634+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:42:43.942293+00:00 exit=0 fresh=True sampledRSSKiB=235408
```

## B46-1 — positive

```text
START 2026-09-07T03:43:12.312926+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:43:14.388019+00:00 exit=0 fresh=True sampledRSSKiB=231440
```

## B47-1 — positive

```text
START 2026-09-07T03:43:38.218994+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:43:40.296590+00:00 exit=0 fresh=True sampledRSSKiB=247088
```

## B48-1 — positive

```text
START 2026-09-07T03:44:04.177244+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:44:06.251174+00:00 exit=0 fresh=True sampledRSSKiB=238400
```

## B49-1 — positive

```text
START 2026-09-07T03:44:31.973470+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:44:40.285791+00:00 exit=0 fresh=True sampledRSSKiB=4390464
```

## B50-1 — positive

```text
START 2026-09-07T03:45:17.253111+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:45:25.557173+00:00 exit=0 fresh=True sampledRSSKiB=4438752
```

## B51-1 — positive

```text
START 2026-09-07T03:46:14.884096+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:46:16.946089+00:00 exit=0 fresh=True sampledRSSKiB=243008
```

## B52-1 — positive

```text
START 2026-09-07T03:46:38.659620+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T03:46:40.729384+00:00 exit=0 fresh=True sampledRSSKiB=251056
```

## B53-1 — positive

```text
START 2026-09-07T03:47:34.584231+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:47:42.874228+00:00 exit=0 fresh=True sampledRSSKiB=2788816
```

## B54-1 — positive

```text
START 2026-09-07T03:48:58.963083+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
10/10: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T03:49:07.267758+00:00 exit=0 fresh=True sampledRSSKiB=2680736
```

## P1-1 — positive

```text
START 2026-09-07T03:53:21.019345+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R177RetirementTransportProbe.idr
2/4: Building DGamma.R172O17OpenParentRootReuseCandidate (research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr)
3/4: Building DGamma.R173UniqueRawNameInsertionsFixtures (research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr)
4/4: Building DGamma.R177RetirementTransportProbe (research-tests/DGamma/R177RetirementTransportProbe.idr)
END 2026-09-07T03:54:10.732505+00:00 exit=0 fresh=True sampledRSSKiB=2711072
```

## P2-1 — charged-proof-rejection

```text
START 2026-09-07T03:55:30.702817+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R177RetirementTransportProbe.idr
4/4: Building DGamma.R177RetirementTransportProbe (research-tests/DGamma/R177RetirementTransportProbe.idr)
Error: While processing right hand side of r177QuietTracePair. Can't solve constraint between: Just (LFinishTag, MkSystemState () (replaceBinding 0 (setFiberRuntime r45ParentBegun (restrictOwnedPreservingOrder r45Spec (ownedValues (fiberTable r45ParentBegun))) (Active (pushLocalUndo r45Spec id id) EmptyView)) r45SourceFinalRegistry)) and if registryWellFormed (MkSystemState (localWorld (MkLocalState (worldState r45SourceFinal) (restrictOwnedPreservingOrder (componentProvisions (fiberComponent r45ParentBegun)) (ownedValues (fiberTable r45ParentBegun))))) (replaceBinding 0 (setFiberRuntime r45ParentBegun (localTable (MkLocalState (worldState r45SourceFinal) (restrictOwnedPreservingOrder (componentProvisions (fiberComponent r45ParentBegun)) (ownedValues (fiberTable r45ParentBegun))))) (Active (pushLocalUndo (componentProvisions (fiberComponent r45ParentBegun)) id id) EmptyView)) (registry r45SourceFinal))) then Just (LFinishTag, MkSystemState (localWorld (MkLocalState (worldState r45SourceFinal) (restrictOwnedPreservingOrder (componentProvisions (fiberComponent r45ParentBegun)) (ownedValues (fiberTable r45ParentBegun))))) (replaceBinding 0 (setFiberRuntime r45ParentBegun (localTable (MkLocalState (worldState r45SourceFinal) (restrictOwnedPreservingOrder (componentProvisions (fiberComponent r45ParentBegun)) (ownedValues (fiberTable r45ParentBegun))))) (Active (pushLocalUndo (componentProvisions (fiberComponent r45ParentBegun)) id id) EmptyView)) (registry r45SourceFinal))) else Nothing.

DGamma.R177RetirementTransportProbe:47:75--47:79
 43 |        (MoreTransitions (Fired r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
 44 |          (MoreTransitions (Fired r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
 45 |            (MoreTransitions (Fired r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) NoTransitions)))))
 46 |    , appendTransitions r45SourceTrace
 47 |        (MoreTransitions (Fired r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) NoTransitions)))
                                                                                ^^^^
END 2026-09-07T03:55:31.734754+00:00 exit=1 fresh=True sampledRSSKiB=0
```

## P2-2 — charged-proof-rejection

```text
START 2026-09-07T03:59:12.136518+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R177RetirementTransportProbe.idr
4/4: Building DGamma.R177RetirementTransportProbe (research-tests/DGamma/R177RetirementTransportProbe.idr)
Error: While processing right hand side of r177QuietTracePair. Can't solve constraint between: Just (OInsertTag, r45SourcePairFinal) and if parentPresent (ChildOf 0) (registry r45AfterBegin) && Delay (provisionsDisjointFrom (componentProvisions r45Child) (registryFibers (registry r45AfterBegin))) then case setFresh 1 (freshFiber r45Child (ChildOf 0)) (registry r45AfterBegin) of { Nothing => Nothing ; Just applied => Just (OInsertTag, MkSystemState (worldState r45AfterBegin) (coeffectAfter applied)) } else Nothing.

DGamma.R177RetirementTransportProbe:65:28--65:32
 61 |           r45SourcePairFinal (MkSystemState () (replaceBinding @{r45NameEq} 0 (setFiberRuntime r45ParentBegun (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec (ownedValues (fiberTable r45ParentBegun))) (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView)) r45SourcePairFinalRegistry)) LFinishTag
 62 |           (preservationTheoremProof r45NameEq r45KeyEq (OInsert 1 (ChildOf 0) r45Child) r45AfterBegin r45SourcePairFinal OInsertTag
 63 |           (preservationTheoremProof r45NameEq r45KeyEq (LBegin 0) r45AfterParent r45AfterBegin LBeginTag
 64 |           (preservationTheoremProof r45NameEq r45KeyEq (OInsert 0 Root r45Parent) r45Initial r45AfterParent OInsertTag
 65 |           Refl Refl) Refl) Refl) Refl)) (MoreTransitions (Fired r45NameEq r45KeyEq (ORetire 1) ORetireTag
                                 ^^^^
END 2026-09-07T03:59:14.224753+00:00 exit=1 fresh=True sampledRSSKiB=663504
```

## P2-3 — charged-proof-rejection

```text
START 2026-09-07T04:02:02.121262+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R177RetirementTransportProbe.idr
4/4: Building DGamma.R177RetirementTransportProbe (research-tests/DGamma/R177RetirementTransportProbe.idr)
Error: While processing right hand side of r177QuietTracePair. Undefined name DGamma.CP3StatementChecks.namedAfter.

DGamma.R177RetirementTransportProbe:37:91--37:127
 33 |    rightFinal : SystemState Nat R45Key R45Value Unit String **
 34 |    (Transitions r45Initial leftFinal, Transitions r45Initial rightFinal))
 35 | r177QuietTracePair = do
 36 |   parentDone <- DGamma.CP3StatementChecks.checkedNamedFire r45NameEq r45KeyEq (LAdvance 0) r45SourcePairFinal
 37 |   childBegun <- DGamma.CP3StatementChecks.checkedNamedFire r45NameEq r45KeyEq (LBegin 1) (DGamma.CP3StatementChecks.namedAfter parentDone)
                                                                                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Did you mean any of: DGamma.CP3StatementChecks.CheckedNamedTransition.namedAfter, or DGamma.CP3StatementChecks.CheckedNamedTransition.(.namedAfter)?
END 2026-09-07T04:02:04.196559+00:00 exit=1 fresh=True sampledRSSKiB=696368
```

## P2-4 — authorized-check-exec-success

```text
START 2026-09-07T04:09:54.214517+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests research-tests/DGamma/R177RetirementTransportProbe.idr --exec putStrLn (case DGamma.R177RetirementTransportProbe.r177QuietTracePair of { Nothing => "R177_P2_PAIR=Nothing"; Just (leftFinal ** rightFinal ** (leftTrace, rightTrace)) => "R177_P2_PAIR=Just; leftQuiet=" ++ show (quiet @{r45NameEq} @{r45KeyEq} leftFinal) ++ "; rightQuiet=" ++ show (quiet @{r45NameEq} @{r45KeyEq} rightFinal) ++ "; leftChildSupported=" ++ show (isSupported @{r45NameEq} @{r45KeyEq} 1 leftFinal) ++ "; rightChildSupported=" ++ show (isSupported @{r45NameEq} @{r45KeyEq} 1 rightFinal) ++ "; leftParentActive=" ++ show (supportedActiveAt @{r45NameEq} 0 leftFinal) ++ "; rightParentActive=" ++ show (supportedActiveAt @{r45NameEq} 0 rightFinal) ++ "; leftLength=" ++ show (transitionCount leftTrace) ++ "; rightLength=" ++ show (transitionCount rightTrace) })
R177_P2_PAIR=Just; leftQuiet=True; rightQuiet=True; leftChildSupported=True; rightChildSupported=False; leftParentActive=True; rightParentActive=True; leftLength=6; rightLength=5
END 2026-09-07T04:09:57.335247+00:00 exit=0 fresh=False sampledRSSKiB=4479152
```

## B55-1 — positive

```text
START 2026-09-07T04:13:21.693460+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:13:22.733600+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B56-1 — positive

```text
START 2026-09-07T04:14:13.920681+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:14:14.959192+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B57-1 — positive

```text
START 2026-09-07T04:14:39.332971+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:14:40.375901+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B58-1 — positive

```text
START 2026-09-07T04:15:08.692156+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:15:09.726767+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B59-1 — positive

```text
START 2026-09-07T04:16:12.077701+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:16:13.117801+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B60-1 — positive

```text
START 2026-09-07T04:16:53.843548+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:16:54.877638+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B61-1 — positive

```text
START 2026-09-07T04:17:47.130288+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:17:48.168854+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B62-1 — positive

```text
START 2026-09-07T04:18:26.204923+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
12/12: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T04:18:28.278745+00:00 exit=0 fresh=True sampledRSSKiB=2120064
```

## B63-1 — positive

```text
START 2026-09-07T04:18:49.204240+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
12/12: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T04:18:51.288300+00:00 exit=0 fresh=True sampledRSSKiB=2122832
```

## B64-1 — positive

```text
START 2026-09-07T04:22:30.353832+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:22:32.420251+00:00 exit=0 fresh=True sampledRSSKiB=298400
```

## B65-1 — positive

```text
START 2026-09-07T04:22:58.399105+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:23:00.497974+00:00 exit=0 fresh=True sampledRSSKiB=265424
```

## B66-1 — positive

```text
START 2026-09-07T04:23:33.274386+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:23:35.340920+00:00 exit=0 fresh=True sampledRSSKiB=288848
```

## B67-1 — positive

```text
START 2026-09-07T04:24:32.805978+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
11/11: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T04:24:41.105860+00:00 exit=0 fresh=True sampledRSSKiB=2555520
```

## B68-1 — positive

```text
START 2026-09-07T04:26:52.854358+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:26:54.934341+00:00 exit=0 fresh=True sampledRSSKiB=226240
```

## B69-1 — positive

```text
START 2026-09-07T04:27:20.089475+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
11/11: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T04:27:28.391253+00:00 exit=0 fresh=True sampledRSSKiB=2753040
```

## B70-1 — positive

```text
START 2026-09-07T04:27:54.387626+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
11/11: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T04:28:03.722268+00:00 exit=0 fresh=True sampledRSSKiB=2926112
```

## B71-1 — positive

```text
START 2026-09-07T04:28:22.961877+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
11/11: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T04:28:31.255651+00:00 exit=0 fresh=True sampledRSSKiB=2516816
```

## B72-1 — positive

```text
START 2026-09-07T04:29:12.149993+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
11/11: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T04:29:21.509880+00:00 exit=0 fresh=True sampledRSSKiB=2935552
```

## B73-1 — positive

```text
START 2026-09-07T04:30:17.610782+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
11/11: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T04:30:26.926156+00:00 exit=0 fresh=True sampledRSSKiB=2933120
```

## B74-1 — positive

```text
START 2026-09-07T04:33:03.634614+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:33:05.716739+00:00 exit=0 fresh=True sampledRSSKiB=222736
```

## B75-1 — positive

```text
START 2026-09-07T04:34:05.147420+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:34:07.223444+00:00 exit=0 fresh=True sampledRSSKiB=203776
```

## B76-1 — positive

```text
START 2026-09-07T04:35:25.737302+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:35:27.805142+00:00 exit=0 fresh=True sampledRSSKiB=187216
```

## B77-1 — positive

```text
START 2026-09-07T04:36:19.152622+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:36:21.247647+00:00 exit=0 fresh=True sampledRSSKiB=238752
```

## B78-1 — positive

```text
START 2026-09-07T04:37:29.982189+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:37:32.074728+00:00 exit=0 fresh=True sampledRSSKiB=248960
```

## B79-1 — positive

```text
START 2026-09-07T04:39:10.013325+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:39:12.091269+00:00 exit=0 fresh=True sampledRSSKiB=235264
```

## B80-1 — positive

```text
START 2026-09-07T04:40:34.767024+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T04:40:36.832720+00:00 exit=0 fresh=True sampledRSSKiB=234752
```

## B81-1 — charged-proof-rejection

```text
START 2026-09-07T04:41:46.312952+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
11/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
12/12: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
Error: Expected ')'.

DGamma.CP5MatchedBirthMetadataSpike:105:11--105:12
 101 |         case matchedEventForward matching leftEvent leftMember of
 102 |           (rightEvent ** (rightMember, matched)) =>
 103 |             (rightEvent ** rightFiber ** (rightMember,
 104 |               (matchedScannedCurrentName name key world error value right (generatedGenerationBijection sameInputs) leftEvent rightEvent matched
 105 |           (rightScannedBirths matching rightEvent rightMember) leftGeneration rightGeneration
                 ^
END 2026-09-07T04:41:53.567806+00:00 exit=1 fresh=True sampledRSSKiB=817856
```

## B81-2 — positive

```text
START 2026-09-07T04:42:36.765848+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
12/12: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T04:42:39.891535+00:00 exit=0 fresh=True sampledRSSKiB=2943424
```

## B82-1 — positive

```text
START 2026-09-07T04:43:40.201790+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
12/12: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T04:43:43.315421+00:00 exit=0 fresh=True sampledRSSKiB=2949536
```

## B83-1 — positive

```text
START 2026-09-07T04:44:59.819930+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
12/12: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T04:45:02.937207+00:00 exit=0 fresh=True sampledRSSKiB=2943200
```

## B84-1 — positive

```text
START 2026-09-07T04:45:23.846214+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
12/12: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T04:45:26.958664+00:00 exit=0 fresh=True sampledRSSKiB=3933472
```

## B85-1 — positive

```text
START 2026-09-07T04:52:30.917854+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T04:52:32.990189+00:00 exit=0 fresh=True sampledRSSKiB=242752
```

## B86-1 — positive

```text
START 2026-09-07T04:53:19.433892+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
4/5: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:53:21.523756+00:00 exit=0 fresh=True sampledRSSKiB=234976
```

## B87-1 — positive

```text
START 2026-09-07T04:53:55.202245+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:53:56.254842+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B88-1 — positive

```text
START 2026-09-07T04:54:23.713178+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:54:24.765396+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B89-1 — positive

```text
START 2026-09-07T04:54:49.356980+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:54:50.394657+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B90-1 — positive

```text
START 2026-09-07T04:55:24.583350+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:55:25.618048+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B91-1 — positive

```text
START 2026-09-07T04:56:04.359093+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:56:05.401019+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B92-1 — positive

```text
START 2026-09-07T04:56:33.333654+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:56:34.374127+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B93-1 — positive

```text
START 2026-09-07T04:56:51.867207+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:56:52.910107+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B94-1 — positive

```text
START 2026-09-07T04:57:50.927141+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:57:51.960193+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B95-1 — charged-proof-rejection

```text
START 2026-09-07T04:58:16.767127+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
Error: While processing right hand side of parentLookupEntryObserved. Undefined name justInjective.

DGamma.CP5RegistrationParentBirthSpike:180:8--180:21
 176 |   Elem (selected, activation) ((candidate, current) :: rest)
 177 | parentLookupEntryObserved name nameEq selected candidate current rest (Yes same) exact recur activation found =
 178 |   replace {p = \entry => Elem entry ((candidate, current) :: rest)}
 179 |     (cong2 MkPair (sym same)
 180 |       (justInjective (trans (sym (parentLookupObserved name nameEq selected candidate current rest (Yes same) exact)) found))) Here
              ^^^^^^^^^^^^^
Did you mean any of: cp3JustInjective (not exported), or pairInjective (not exported)?
END 2026-09-07T04:58:17.804484+00:00 exit=1 fresh=True sampledRSSKiB=0
```

## B95-2 — positive

```text
START 2026-09-07T04:58:32.021655+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:58:33.058893+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B96-1 — positive

```text
START 2026-09-07T04:58:54.850661+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:58:55.885692+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B97-1 — positive

```text
START 2026-09-07T04:59:44.140827+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T04:59:45.174312+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B98-1 — positive

```text
START 2026-09-07T05:00:47.474183+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T05:00:48.516695+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B99-1 — positive

```text
START 2026-09-07T05:03:03.602464+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T05:03:04.644676+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B100-1 — positive

```text
START 2026-09-07T05:03:30.466360+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T05:03:31.501180+00:00 exit=0 fresh=True sampledRSSKiB=0
```

## B101-1 — positive

```text
START 2026-09-07T05:06:55.411741+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5RegistrationParentBirthSpike.idr
3/5: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
4/5: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
5/5: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
END 2026-09-07T05:06:59.558791+00:00 exit=0 fresh=True sampledRSSKiB=374256
```

## B102-1 — charged-proof-rejection

```text
START 2026-09-07T05:08:51.395988+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
12/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
Error: While processing right hand side of registrationSideFoldParentBirth. Undefined name plusZeroRightNeutral.

DGamma.CP5ConfluenceRenamingCompositionSpike:3198:298--3198:318
 3194 |         (\wanted, occurrence => embedding wanted (currentBirthPrependLocation name key world error value step rest wanted occurrence))
 3195 |         (\wanted, occurrence => trans (embeddingExact wanted (currentBirthPrependLocation name key world error value step rest wanted occurrence))
 3196 |               (trans (cong (ordinal +) (currentBirthPrependOrdinal name key world error value step rest wanted occurrence))
 3197 |                 (sym (plusSuccRightSucc ordinal (locatedActionOrdinal occurrence)))))
 3198 |         (registrationIndexBirthAction name key world error value nameEq global ordinal action index (embedding action (MkLocatedActionOccurrence _ _ NoTransitions step rest actionExact Refl)) (trans (embeddingExact action (MkLocatedActionOccurrence _ _ NoTransitions step rest actionExact Refl)) (plusZeroRightNeutral ordinal)) births)
                                                                                                                                                                                                                                                                                                                 ^^^^^^^^^^^^^^^^^^^^
END 2026-09-07T05:08:59.681038+00:00 exit=1 fresh=True sampledRSSKiB=791696
```

## B102-2 — positive

```text
START 2026-09-07T05:09:19.061118+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
12/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T05:09:28.409473+00:00 exit=0 fresh=True sampledRSSKiB=4479936
```

## B103-1 — positive

```text
START 2026-09-07T05:10:16.893894+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
12/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T05:10:26.206139+00:00 exit=0 fresh=True sampledRSSKiB=4450736
```

## B104-1 — positive

```text
START 2026-09-07T05:11:14.310747+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
12/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T05:11:23.627853+00:00 exit=0 fresh=True sampledRSSKiB=4453968
```

## B105-1 — positive

```text
START 2026-09-07T05:11:48.883748+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
12/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T05:11:58.215784+00:00 exit=0 fresh=True sampledRSSKiB=3662960
```

## B106-1 — positive

```text
START 2026-09-07T05:12:31.651150+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
12/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T05:12:40.973744+00:00 exit=0 fresh=True sampledRSSKiB=3912272
```

## B107-1 — positive

```text
START 2026-09-07T05:13:00.941453+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
12/12: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
END 2026-09-07T05:13:10.277583+00:00 exit=0 fresh=True sampledRSSKiB=3980400
```

## B108-1 — positive

```text
START 2026-09-07T05:14:47.268029+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:14:50.385771+00:00 exit=0 fresh=True sampledRSSKiB=3971216
```

## B109-1 — positive

```text
START 2026-09-07T05:15:30.542202+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:15:33.650860+00:00 exit=0 fresh=True sampledRSSKiB=3936896
```

## B110-1 — positive

```text
START 2026-09-07T05:16:27.426317+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:16:30.542759+00:00 exit=0 fresh=True sampledRSSKiB=3692816
```

## B111-1 — positive

```text
START 2026-09-07T05:20:24.178693+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T05:20:27.304737+00:00 exit=0 fresh=True sampledRSSKiB=369600
```

## B112-1 — positive

```text
START 2026-09-07T05:21:32.507944+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T05:21:34.587972+00:00 exit=0 fresh=True sampledRSSKiB=250400
```

## B113-1 — positive

```text
START 2026-09-07T05:22:07.948443+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5CurrentGenerationBirthSpike.idr
3/3: Building DGamma.CP5CurrentGenerationBirthSpike (research/DGamma/CP5CurrentGenerationBirthSpike.idr)
END 2026-09-07T05:22:10.029962+00:00 exit=0 fresh=True sampledRSSKiB=240576
```

## B114-1 — positive

```text
START 2026-09-07T05:22:48.324183+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T05:22:50.395622+00:00 exit=0 fresh=True sampledRSSKiB=239584
```

## B115-1 — positive

```text
START 2026-09-07T05:25:19.245170+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T05:25:21.328581+00:00 exit=0 fresh=True sampledRSSKiB=240736
```

## B116-1 — positive

```text
START 2026-09-07T05:26:20.694980+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ImmutableBirthMetadataSpike.idr
4/4: Building DGamma.CP5ImmutableBirthMetadataSpike (research/DGamma/CP5ImmutableBirthMetadataSpike.idr)
END 2026-09-07T05:26:22.759114+00:00 exit=0 fresh=True sampledRSSKiB=236448
```

## B117-1 — positive

```text
START 2026-09-07T05:27:37.559594+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
 5/13: Building DGamma.CP5RegistrationParentBirthSpike (research/DGamma/CP5RegistrationParentBirthSpike.idr)
12/13: Building DGamma.CP5ConfluenceRenamingCompositionSpike (research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr)
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:27:47.907149+00:00 exit=0 fresh=True sampledRSSKiB=1860304
```

## B118-1 — positive

```text
START 2026-09-07T05:28:49.886444+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:28:52.991459+00:00 exit=0 fresh=True sampledRSSKiB=805072
```

## B119-1 — positive

```text
START 2026-09-07T05:30:43.285616+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:30:47.447138+00:00 exit=0 fresh=True sampledRSSKiB=310016
```

## B120-1 — positive

```text
START 2026-09-07T05:31:15.263845+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:31:19.416565+00:00 exit=0 fresh=True sampledRSSKiB=2936080
```

## B121-1 — positive

```text
START 2026-09-07T05:32:39.113285+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:32:43.286600+00:00 exit=0 fresh=True sampledRSSKiB=2946288
```

## B122-1 — positive

```text
START 2026-09-07T05:33:19.846588+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:33:23.996483+00:00 exit=0 fresh=True sampledRSSKiB=3975248
```

## F3-FinalCanonicalSort — positive

```text
START 2026-09-07T05:36:11.458308+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceCanonicalSortSpike.idr
8/8: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sorted is shadowing Data.List.sorted

DGamma.CP5ConfluenceCanonicalSortSpike:4658:3--4662:39
 4658 | 0 abstractTwoBirthOneWithdrawalAccounting :
 4659 |   (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
 4660 |     nameEq keyEq original reduction ordering sorted) ->
 4661 |   OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
 4662 |     original reduction ordering sorted
END 2026-09-07T05:37:07.375055+00:00 exit=0 fresh=True sampledRSSKiB=20152992
```

## F4-FinalUniqueCapital — positive

```text
START 2026-09-07T05:37:34.250731+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5UniqueRawNameCanonicalCapital.idr
13/15: Building DGamma.CP5ConfluenceCrossTraceSpike (research/DGamma/CP5ConfluenceCrossTraceSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:40:3--40:68
 36 |
 37 | public export
 38 | data CertifiedActorPermutation :
 39 |   (name : Type) -> List name -> List name -> Type where
 40 |   ActorPermutationDone : CertifiedActorPermutation name order order
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:41:3--44:48
 41 |   ActorPermutationStep :
 42 |     AdjacentActorOrderSwap name before middle ->
 43 |     CertifiedActorPermutation name middle after ->
 44 |     CertifiedActorPermutation name before after

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:274:1--277:77
 274 | transitionPrefixLength : (earlierTrace : Transitions initial before) ->
 275 |   (step : Transition before after) ->
 276 |   transitionCount (appendTransitions earlierTrace
 277 |     (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  order is shadowing Control.Order.order

DGamma.CP5ConfluenceCrossTraceSpike:736:3--742:55
 736 |   OperationalActorDone :
 737 |     (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
 738 |       order trace) ->
 739 |     (premises : ReplayInvariantBundle name key world error value protocol nameEq
 740 |       keyEq trace) ->
 741 |     OperationalActorPermutation name key world error value protocol nameEq keyEq

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  after is shadowing DGamma.Core.Applied.after

DGamma.CP5ConfluenceCrossTraceSpike:743:3--759:35
 743 |   OperationalActorStep :
 744 |     (orderSwap : AdjacentActorOrderSwap name before middle) ->
 745 |     (restCertificate : CertifiedActorPermutation name middle after) ->
 746 |     (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
 747 |       before sourceTrace) ->
 748 |     (sourcePremises : ReplayInvariantBundle name key world error value protocol

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1219:3--1227:41
 1219 | 0 permutationReplayCorrespondence :
 1220 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1221 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1222 |       rightCapital matching} ->
 1223 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1224 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  sameInputs is shadowing DGamma.CP3.CanonicalSchedule.sameInputs

DGamma.CP5ConfluenceCrossTraceSpike:1233:3--1241:41
 1233 | 0 permutationOccurrenceCorrespondence :
 1234 |   {operational : CertifiedOperationalCanonicalPermutation name key world error
 1235 |     value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
 1236 |       rightCapital matching} ->
 1237 |   PermutedCanonicalExecution name key world error value protocol nameEq keyEq
 1238 |     leftTrace rightTrace sameInputs leftCapital rightCapital operational ->

15/15: Building DGamma.CP5UniqueRawNameCanonicalCapital (research/DGamma/CP5UniqueRawNameCanonicalCapital.idr)
END 2026-09-07T05:37:40.477379+00:00 exit=0 fresh=True sampledRSSKiB=4624768
```

## F5-FinalFullPipeline — positive

```text
START 2026-09-07T05:39:31.826155+00:00 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R8FullPipeline.idr
1/1: Building DGamma.R8FullPipeline (research-tests/DGamma/R8FullPipeline.idr)
END 2026-09-07T05:41:12.392978+00:00 exit=0 fresh=True sampledRSSKiB=38703008
```

## F6-FinalGeneratedStaticCoherence — positive

```text
START 2026-09-07T05:44:16.943294+00:00 idris2 --source-dir src --source-dir research --check research/DGamma/CP5MatchedBirthMetadataSpike.idr
13/13: Building DGamma.CP5MatchedBirthMetadataSpike (research/DGamma/CP5MatchedBirthMetadataSpike.idr)
END 2026-09-07T05:44:21.088898+00:00 exit=0 fresh=True sampledRSSKiB=3513568
```

## F7-SeededPackage207 — positive

```text
START 2026-09-07T05:44:29.358867+00:00 idris2 --build dgamma.ipkg

END 2026-09-07T05:44:45.905716+00:00 exit=0 fresh=True sampledRSSKiB=224144
```
