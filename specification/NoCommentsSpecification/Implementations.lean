module

public import LeanIntent.Implementation
public import NoCommentsSpecification.Deliverables
public import NoCommentsSpecification.Refinement.Core
public import NoCommentsSpecification.Refinement.Config
public import NoCommentsSpecification.Refinement.Ratchet

@[expose] public section

namespace NoCommentsSpecification.Implementations

open LeanIntent
open NoComments
open NoCommentsSpecification.Deliverables
open NoCommentsSpecification.Refinement.Core
open NoCommentsSpecification.Refinement.Config
open NoCommentsSpecification.Refinement.Ratchet

def isFingerprintImplementation : Implementation isFingerprintDeliverable where
  subject := NoComments.Core.isFingerprint
  fulfils := isFingerprint_fulfilled

def fingerprintImplementation : Implementation fingerprintDeliverable where
  subject := NoComments.Core.fingerprint
  fulfils := fingerprint_fulfilled

def checkTokenImplementation : Implementation checkTokenDeliverable where
  subject := NoComments.Core.checkToken
  fulfils := checkToken_fulfilled

def collectRangesImplementation : Implementation collectRangesDeliverable where
  subject := NoComments.Core.collectRanges
  fulfils := collectRanges_fulfilled

def sourceOrderImplementation : Implementation sourceOrderDeliverable where
  subject := NoComments.Core.sourceOrder
  fulfils := sourceOrder_fulfilled

def distinctCommentLinesImplementation : Implementation distinctCommentLinesDeliverable where
  subject := NoComments.Core.distinctCommentLines
  fulfils := distinctCommentLines_fulfilled

def firstOutOfOrderImplementation : Implementation firstOutOfOrderDeliverable where
  subject := NoComments.Core.firstOutOfOrder
  fulfils := firstOutOfOrder_fulfilled

def sortFingerprintsImplementation : Implementation sortFingerprintsDeliverable where
  subject := NoComments.Core.sortFingerprints
  fulfils := sortFingerprints_fulfilled

def missingFromImplementation : Implementation missingFromDeliverable where
  subject := NoComments.Core.missingFrom
  fulfils := missingFrom_fulfilled

def parseConfigImplementation : Implementation parseConfigDeliverable where
  subject := NoComments.Config.parseConfigJson
  fulfils := parseConfigJson_fulfilled

def classifyFileImplementation : Implementation classifyFileDeliverable where
  subject := NoComments.Config.classifyFile
  fulfils := classifyFile_fulfilled

def classifyTrackedImplementation : Implementation classifyTrackedDeliverable where
  subject := NoComments.Config.classifyTrackedFiles
  fulfils := classifyTrackedFiles_fulfilled

def analyzeCommentsImplementation : Implementation analyzeCommentsDeliverable where
  subject := NoComments.RatchetCore.analyzeComments
  fulfils := analyzeComments_fulfilled

def parseRatchetImplementation : Implementation parseRatchetDeliverable where
  subject := NoComments.RatchetCore.parseRatchetJson
  fulfils := parseRatchetJson_fulfilled

def checkExactSyncImplementation : Implementation checkExactSyncDeliverable where
  subject := NoComments.RatchetCore.checkExactSync
  fulfils := checkExactSync_fulfilled

def checkMonotonicFileImplementation : Implementation checkMonotonicFileDeliverable where
  subject := NoComments.RatchetCore.checkMonotonicFile
  fulfils := checkMonotonicFile_fulfilled

def validateCheckImplementation : Implementation validateCheckDeliverable where
  subject := NoComments.RatchetCore.validateCheck
  fulfils := validateCheck_fulfilled

end NoCommentsSpecification.Implementations
