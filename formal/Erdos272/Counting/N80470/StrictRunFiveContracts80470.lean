module

public import Erdos272.Counting.N80470.StrictRunTransfer80470
public import Erdos272.Arithmetic.N86412.StrictRunNumericBridge86412
public import Erdos272.Resources.N82427.SourceAtlas82427
public import Erdos272.Arithmetic.N80470.StrictRunFiveNumeric80470

@[expose] public section

namespace JSP233.StrictRunFiveContracts80470
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208 SourceContract86412
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def high00 : CertifiedContract where
  contract := ⟨87,17,24310⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=19) (by decide)
      hN hground hS hsize hdefect

def run00 : CertifiedContract where
  contract := ⟨86,31,24246⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan StrictRunFiveNumeric80470.plan00)
      (StrictRunNumericBridge86412.conditions_sound StrictRunFiveNumeric80470.checked00)
      high00 (by decide) (by decide) (by decide) hN hground hS hsize hdefect


def high01 : CertifiedContract where
  contract := ⟨87,41,38764⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=50) (by decide)
      hN hground hS hsize hdefect

def run01 : CertifiedContract where
  contract := ⟨86,41,38220⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan StrictRunFiveNumeric80470.plan01)
      (StrictRunNumericBridge86412.conditions_sound StrictRunFiveNumeric80470.checked01)
      high01 (by decide) (by decide) (by decide) hN hground hS hsize hdefect


def high02 : CertifiedContract where
  contract := ⟨87,49,48484⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=74) (by decide)
      hN hground hS hsize hdefect

def run02 : CertifiedContract where
  contract := ⟨86,49,48000⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan StrictRunFiveNumeric80470.plan02)
      (StrictRunNumericBridge86412.conditions_sound StrictRunFiveNumeric80470.checked02)
      high02 (by decide) (by decide) (by decide) hN hground hS hsize hdefect


def high03 : CertifiedContract where
  contract := ⟨87,55,56624⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=92) (by decide)
      hN hground hS hsize hdefect

def run03 : CertifiedContract where
  contract := ⟨86,55,55942⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan StrictRunFiveNumeric80470.plan03)
      (StrictRunNumericBridge86412.conditions_sound StrictRunFiveNumeric80470.checked03)
      high03 (by decide) (by decide) (by decide) hN hground hS hsize hdefect


def high04 : CertifiedContract where
  contract := ⟨87,54,55262⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact SourceAtlas82427.actual_source (i:=89) (by decide)
      hN hground hS hsize hdefect

def run04 : CertifiedContract where
  contract := ⟨86,54,54522⟩
  actual := by
    intro N S hN hground hS hsize hdefect
    exact StrictRunTransfer80470.actual_run_plan_source
      (RunNumericBridge88404.toPlan StrictRunFiveNumeric80470.plan04)
      (StrictRunNumericBridge86412.conditions_sound StrictRunFiveNumeric80470.checked04)
      high04 (by decide) (by decide) (by decide) hN hground hS hsize hdefect


end
end JSP233.StrictRunFiveContracts80470
