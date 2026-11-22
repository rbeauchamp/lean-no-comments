module

public import LeanIntent.Execution
public import NoCommentsSpecification.Deliverables

@[expose] public section

namespace NoCommentsSpecification.Execution

open LeanIntent
open NoCommentsSpecification.Deliverables

def isFingerprintRuns : Runs isFingerprintDeliverable where
  executable := `«no-comments»

def fingerprintRuns : Runs fingerprintDeliverable where
  executable := `«no-comments»

def checkTokenRuns : Runs checkTokenDeliverable where
  executable := `«no-comments»

def collectRangesRuns : Runs collectRangesDeliverable where
  executable := `«no-comments»

def sourceOrderRuns : Runs sourceOrderDeliverable where
  executable := `«no-comments»

def distinctCommentLinesRuns : Runs distinctCommentLinesDeliverable where
  executable := `«no-comments»

def firstOutOfOrderRuns : Runs firstOutOfOrderDeliverable where
  executable := `«no-comments»

def sortFingerprintsRuns : Runs sortFingerprintsDeliverable where
  executable := `«no-comments»

def missingFromRuns : Runs missingFromDeliverable where
  executable := `«no-comments»

def parseConfigRuns : Runs parseConfigDeliverable where
  executable := `«no-comments»

def classifyFileRuns : Runs classifyFileDeliverable where
  executable := `«no-comments»

def classifyTrackedRuns : Runs classifyTrackedDeliverable where
  executable := `«no-comments»

def analyzeCommentsRuns : Runs analyzeCommentsDeliverable where
  executable := `«no-comments»

def parseRatchetRuns : Runs parseRatchetDeliverable where
  executable := `«no-comments»

def checkExactSyncRuns : Runs checkExactSyncDeliverable where
  executable := `«no-comments»

def checkMonotonicFileRuns : Runs checkMonotonicFileDeliverable where
  executable := `«no-comments»

def validateCheckRuns : Runs validateCheckDeliverable where
  executable := `«no-comments»

end NoCommentsSpecification.Execution
