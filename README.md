# Torn Analytics — Official Releases

This repository is the official stable release channel for Torn Analytics.

## Install URL

```text
https://raw.githubusercontent.com/C33J4Y01/Torn-analytics-releases/main/torn-analytics.user.js
```

## Update metadata URL

```text
https://raw.githubusercontent.com/C33J4Y01/Torn-analytics-releases/main/torn-analytics.meta.js
```

`torn-analytics.user.js` is the complete executable userscript.
`torn-analytics.meta.js` is a header-only version-check artifact and is not a
second runtime.

## Release contract

Stable releases are promoted from the private development repository only after
build parity, protected invariants, regression tests, review, and the applicable
device gate pass. The public full userscript and metadata blobs must exactly
match their validated private counterparts.

Public validation requires:

- valid JavaScript syntax for both artifacts
- identical userscript headers and semantic versions
- a metadata-first `@updateURL`
- the full userscript as `@downloadURL`
- basic secret-exposure checks

The public repository does not generate or patch release artifacts.

## Privacy

This repository contains no Torn API keys, player logs, exports, account
analytics, local settings, recovery material, or development history. Torn
Analytics stores player history locally on the user's device.

## Authenticity

Use only the install URL above under the GitHub owner `C33J4Y01`. Modified forks
and similarly named scripts are not official releases.

## Licensing

No license is granted for copying, modifying, redistributing, or selling this
code. All rights are reserved unless a license is added later.
