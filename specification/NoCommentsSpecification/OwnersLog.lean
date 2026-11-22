module

public import LeanIntent.Confirmation
public import NoCommentsSpecification.OwnersLogEntriesCore
public import NoCommentsSpecification.OwnersLogEntriesConfig
public import NoCommentsSpecification.OwnersLogEntriesRatchet

@[expose] public section

namespace NoCommentsSpecification.OwnersLog

open LeanIntent

def noCommentsOwnersLog : OwnersLog where
  statements := [
    OwnersLogEntriesCore.ownersStmt,
    OwnersLogEntriesCore.delegationStmt,
    OwnersLogEntriesCore.originStmt,
    OwnersLogEntriesCore.toolSpecVerifyStmt,
    OwnersLogEntriesCore.toolRootNoCommentsStmt,
    OwnersLogEntriesCore.toolTestListingStmt,
    OwnersLogEntriesCore.restatement_isFingerprint,
    OwnersLogEntriesCore.restatement_fingerprint,
    OwnersLogEntriesCore.delegated_fingerprint,
    OwnersLogEntriesCore.restatement_checkToken,
    OwnersLogEntriesCore.delegated_checkToken,
    OwnersLogEntriesCore.restatement_collectRanges,
    OwnersLogEntriesCore.delegated_collectRanges,
    OwnersLogEntriesCore.restatement_sourceOrder,
    OwnersLogEntriesCore.restatement_distinctCommentLines,
    OwnersLogEntriesCore.restatement_firstOutOfOrder,
    OwnersLogEntriesCore.restatement_sortFingerprints,
    OwnersLogEntriesCore.restatement_missingFrom,
    OwnersLogEntriesCore.delegated_missingFrom,
    OwnersLogEntriesConfig.restatement_parseConfig,
    OwnersLogEntriesConfig.delegated_parseConfig,
    OwnersLogEntriesConfig.restatement_classifyFile,
    OwnersLogEntriesConfig.delegated_classifyFile,
    OwnersLogEntriesConfig.restatement_classifyTracked,
    OwnersLogEntriesConfig.delegated_classifyTracked,
    OwnersLogEntriesRatchet.restatement_analyzeComments,
    OwnersLogEntriesRatchet.restatement_parseRatchet,
    OwnersLogEntriesRatchet.delegated_parseRatchet,
    OwnersLogEntriesRatchet.restatement_checkExactSync,
    OwnersLogEntriesRatchet.delegated_checkExactSync,
    OwnersLogEntriesRatchet.restatement_checkMonotonicFile,
    OwnersLogEntriesRatchet.delegated_checkMonotonicFile,
    OwnersLogEntriesRatchet.restatement_validateCheck,
    OwnersLogEntriesRatchet.delegated_validateCheck
  ]

end NoCommentsSpecification.OwnersLog
