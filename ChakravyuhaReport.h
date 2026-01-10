#pragma once
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Triple.h"
#include <ctime>
#include <iomanip>
#include <sstream>
#include <string>
#include <vector>

namespace chakravyuha {

struct ReportData {
  std::string inputFile;
  std::string outputFile = "obfuscated.ll";
  std::string targetPlatform;
  std::string obfuscationLevel = "medium";
  bool enableStringEncryption = false;
  bool enableControlFlowFlattening = false;
  bool enableFakeCodeInsertion = false;
  unsigned cyclesCompleted = 1;

  // Total IR size metrics
  uint64_t originalIRSize = 0;
  uint64_t obfuscatedIRSize = 0;

  // String encryption metrics
  unsigned stringsEncrypted = 0;
  uint64_t originalIRStringDataSize = 0;
  uint64_t obfuscatedIRStringDataSize = 0;
  std::string stringMethod;

  // Control flow flattening metrics
  unsigned flattenedFunctions = 0;
  unsigned flattenedBlocks = 0;
  unsigned skippedFunctions = 0;

  // Fake code insertion metrics
  unsigned fakeCodeBlocksInserted = 0;

  std::vector<std::string> passesRun;

  static ReportData &get() {
    static ReportData R;
    return R;
  }
};

// Centralized function to detect unsafe constructs.
inline bool shouldSkipFunction(llvm::Function &F) {
  for (llvm::BasicBlock &BB : F) {
    for (llvm::Instruction &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->isInlineAsm()) {
          return true;
        }
        llvm::Function *CalledFunc = CI->getCalledFunction();
        if (CalledFunc && (CalledFunc->getName() == "setjmp" ||
                           CalledFunc->getName() == "_setjmp" ||
                           CalledFunc->getName() == "longjmp")) {
          return true;
        }
      }
    }
  }
  return false;
}

inline std::string esc(const std::string &S) {
  std::string T;
  T.reserve(S.size());
  for (char c : S) {
    if (c == '\\')
      T += "\\\\";
    else if (c == '"')
      T += "\\\"";
    else
      T += c;
  }
  return T;
}

inline std::string nowUtcIso8601() {
  std::time_t t = std::time(nullptr);
  std::tm tm{};
#if defined(_WIN32)
  gmtime_s(&tm, &t);
#else
  gmtime_r(&t, &tm);
#endif
  char b[24];
  std::strftime(b, sizeof(b), "%Y-%m-%dT%H:%M:%SZ", &tm);
  return b;
}

inline void finalizeDefaults(llvm::Module &M) {
  auto &R = ReportData::get();

  if (R.inputFile.empty()) {
    const std::string &SF = M.getSourceFileName();
    R.inputFile = SF.empty() ? std::string("<stdin>") : SF;
  }

  if (R.targetPlatform.empty()) {
    llvm::Triple T(M.getTargetTriple());
    R.targetPlatform = T.isOSWindows() ? "windows" : "linux";
  }
}

// Helper function to calculate the size of the Module's textual IR
// representation.
inline uint64_t getModuleIRSize(llvm::Module &M) {
  std::string str;
  llvm::raw_string_ostream os(str);
  M.print(os, nullptr);
  return str.size();
}

inline void emitReportJSON(llvm::Module &M) {
  finalizeDefaults(M);
  auto &R = ReportData::get();

  // Calculate final IR size at the last possible moment.
  R.obfuscatedIRSize = getModuleIRSize(M);

  // Percentage change calculations
  double strChangePct = 0.0;
  if (R.originalIRStringDataSize != 0) {
    strChangePct = ((double)R.obfuscatedIRStringDataSize -
                    (double)R.originalIRStringDataSize) /
                   (double)R.originalIRStringDataSize * 100.0;
  }

  double totalChangePct = 0.0;
  if (R.originalIRSize != 0) {
    totalChangePct = ((double)R.obfuscatedIRSize - (double)R.originalIRSize) /
                     (double)R.originalIRSize * 100.0;
  }

  std::string strChangeStr = llvm::formatv("{0:F2}%", strChangePct);
  std::string totalChangeStr = llvm::formatv("{0:F2}%", totalChangePct);

  // Build JSON Tree
  llvm::json::Object root;

  root["inputFile"] = R.inputFile;
  root["outputFile"] = R.outputFile;
  root["timestamp"] = nowUtcIso8601();

  root["inputParameters"] = llvm::json::Object{
      {"obfuscationLevel", R.obfuscationLevel},
      {"targetPlatform", R.targetPlatform},
      {"enableStringEncryption", R.enableStringEncryption},
      {"enableControlFlowFlattening", R.enableControlFlowFlattening},
      {"enableFakeCodeInsertion", R.enableFakeCodeInsertion}};

  root["outputAttributes"] = llvm::json::Object{
      {"originalIRSize", llvm::formatv("{0} bytes", R.originalIRSize)},
      {"obfuscatedIRSize", llvm::formatv("{0} bytes", R.obfuscatedIRSize)},
      {"totalIRSizeChange", totalChangeStr},
      {"originalIRStringDataSize",
       llvm::formatv("{0} bytes", R.originalIRStringDataSize)},
      {"obfuscatedIRStringDataSize",
       llvm::formatv("{0} bytes", R.obfuscatedIRStringDataSize)},
      {"stringDataSizeChange", strChangeStr}};

  llvm::json::Array passesRunArr;
  for (const auto &pass : R.passesRun) {
    passesRunArr.push_back(pass);
  }

  root["obfuscationMetrics"] = llvm::json::Object{
      {"cyclesCompleted", R.cyclesCompleted},
      {"passesRun", std::move(passesRunArr)},
      {"stringEncryption",
       llvm::json::Object{
           {"count", R.stringsEncrypted},
           {"method", R.stringMethod.empty() ? "N/A" : R.stringMethod}}},
      {"controlFlowFlattening",
       llvm::json::Object{{"flattenedFunctions", R.flattenedFunctions},
                          {"flattenedBlocks", R.flattenedBlocks},
                          {"skippedFunctions", R.skippedFunctions}}},
      {"fakeCodeInsertion",
       llvm::json::Object{{"insertedBlocks", R.fakeCodeBlocksInserted}}}};

  // {0:2} formats json with a 2-space indentation
  llvm::errs() << llvm::formatv("{0:2}", llvm::json::Value(std::move(root)))
               << "\n";
}

} // namespace chakravyuha
