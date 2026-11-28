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
  meets := isFingerprint_meets

def fingerprintImplementation : Implementation fingerprintDeliverable where
  subject := NoComments.Core.fingerprint
  meets := fingerprint_meets

def checkTokenImplementation : Implementation checkTokenDeliverable where
  subject := NoComments.Core.checkToken
  meets := checkToken_meets

def collectRangesImplementation : Implementation collectRangesDeliverable where
  subject := NoComments.Core.collectRanges
  meets := collectRanges_meets

def sourceOrderImplementation : Implementation sourceOrderDeliverable where
  subject := NoComments.Core.sourceOrder
  meets := sourceOrder_meets

def distinctCommentLinesImplementation : Implementation distinctCommentLinesDeliverable where
  subject := NoComments.Core.distinctCommentLines
  meets := distinctCommentLines_meets

def firstOutOfOrderImplementation : Implementation firstOutOfOrderDeliverable where
  subject := NoComments.Core.firstOutOfOrder
  meets := firstOutOfOrder_meets

def sortFingerprintsImplementation : Implementation sortFingerprintsDeliverable where
  subject := NoComments.Core.sortFingerprints
  meets := sortFingerprints_meets

def missingFromImplementation : Implementation missingFromDeliverable where
  subject := NoComments.Core.missingFrom
  meets := missingFrom_meets

def parseConfigImplementation : Implementation parseConfigDeliverable where
  subject := NoComments.Config.parseConfigJson
  meets := parseConfigJson_meets

def classifyFileImplementation : Implementation classifyFileDeliverable where
  subject := NoComments.Config.classifyFile
  meets := classifyFile_meets

def classifyTrackedImplementation : Implementation classifyTrackedDeliverable where
  subject := NoComments.Config.classifyTrackedFiles
  meets := classifyTrackedFiles_meets

def analyzeCommentsImplementation : Implementation analyzeCommentsDeliverable where
  subject := NoComments.RatchetCore.analyzeComments
  meets := analyzeComments_meets

def parseRatchetImplementation : Implementation parseRatchetDeliverable where
  subject := NoComments.RatchetCore.parseRatchetJson
  meets := parseRatchetJson_meets

def checkExactSyncImplementation : Implementation checkExactSyncDeliverable where
  subject := NoComments.RatchetCore.checkExactSync
  meets := checkExactSync_meets

def checkMonotonicFileImplementation : Implementation checkMonotonicFileDeliverable where
  subject := NoComments.RatchetCore.checkMonotonicFile
  meets := checkMonotonicFile_meets

def validateCheckImplementation : Implementation validateCheckDeliverable where
  subject := NoComments.RatchetCore.validateCheck
  meets := validateCheck_meets

end NoCommentsSpecification.Implementations
