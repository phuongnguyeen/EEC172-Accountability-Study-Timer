################################################################################
# Automatically-generated file. Do not edit!
################################################################################

SHELL = cmd.exe

# Each subdirectory must supply rules for building sources it contributes
%.obj: ../%.c $(GEN_OPTS) | $(GEN_FILES) $(GEN_MISC_FILES)
	@echo 'Building file: "$<"'
	@echo 'Invoking: Arm Compiler'
	"C:/Users/phpng/ti/cc1250/ccs/tools/compiler/ti-cgt-arm_20.2.7.LTS/bin/armcl" -mv7M4 --code_state=16 --float_support=none -me -Ooff --include_path="C:/Users/phpng/ti/eec172 workspace/final_projectwuart" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/include" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/source" --include_path="C:/Users/phpng/ti/cc3200-sdk/driverlib/" --include_path="C:/Users/phpng/ti/cc3200-sdk/inc/" --include_path="C:/Users/phpng/ti/cc3200-sdk/example/common/" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink_extlib/provisioninglib" --include_path="C:/Users/phpng/ti/cc1250/ccs/tools/compiler/ti-cgt-arm_20.2.7.LTS/include" --define=ccs --define=cc3200 -g --diag_warning=225 --diag_wrap=off --display_error_number --abi=eabi --preproc_with_compile --preproc_dependency="$(basename $(<F)).d_raw" $(GEN_OPTS__FLAG) "$<"
	@echo 'Finished building: "$<"'
	@echo ' '

i2c_if.obj: C:/Users/phpng/ti/cc3200-sdk/example/common/i2c_if.c $(GEN_OPTS) | $(GEN_FILES) $(GEN_MISC_FILES)
	@echo 'Building file: "$<"'
	@echo 'Invoking: Arm Compiler'
	"C:/Users/phpng/ti/cc1250/ccs/tools/compiler/ti-cgt-arm_20.2.7.LTS/bin/armcl" -mv7M4 --code_state=16 --float_support=none -me -Ooff --include_path="C:/Users/phpng/ti/eec172 workspace/final_projectwuart" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/include" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/source" --include_path="C:/Users/phpng/ti/cc3200-sdk/driverlib/" --include_path="C:/Users/phpng/ti/cc3200-sdk/inc/" --include_path="C:/Users/phpng/ti/cc3200-sdk/example/common/" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink_extlib/provisioninglib" --include_path="C:/Users/phpng/ti/cc1250/ccs/tools/compiler/ti-cgt-arm_20.2.7.LTS/include" --define=ccs --define=cc3200 -g --diag_warning=225 --diag_wrap=off --display_error_number --abi=eabi --preproc_with_compile --preproc_dependency="i2c_if.d_raw" $(GEN_OPTS__FLAG) "$<"
	@echo 'Finished building: "$<"'
	@echo ' '

network_common.obj: C:/Users/phpng/ti/cc3200-sdk/example/common/network_common.c $(GEN_OPTS) | $(GEN_FILES) $(GEN_MISC_FILES)
	@echo 'Building file: "$<"'
	@echo 'Invoking: Arm Compiler'
	"C:/Users/phpng/ti/cc1250/ccs/tools/compiler/ti-cgt-arm_20.2.7.LTS/bin/armcl" -mv7M4 --code_state=16 --float_support=none -me -Ooff --include_path="C:/Users/phpng/ti/eec172 workspace/final_projectwuart" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/include" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink/source" --include_path="C:/Users/phpng/ti/cc3200-sdk/driverlib/" --include_path="C:/Users/phpng/ti/cc3200-sdk/inc/" --include_path="C:/Users/phpng/ti/cc3200-sdk/example/common/" --include_path="C:/Users/phpng/ti/cc3200-sdk/simplelink_extlib/provisioninglib" --include_path="C:/Users/phpng/ti/cc1250/ccs/tools/compiler/ti-cgt-arm_20.2.7.LTS/include" --define=ccs --define=cc3200 -g --diag_warning=225 --diag_wrap=off --display_error_number --abi=eabi --preproc_with_compile --preproc_dependency="network_common.d_raw" $(GEN_OPTS__FLAG) "$<"
	@echo 'Finished building: "$<"'
	@echo ' '


