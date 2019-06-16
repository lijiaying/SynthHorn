set (Z3_TAG "z3-4.5.0" CACHE STRING "Z3 git tag to use")
set (Z3_REPO "https://github.com/Z3Prover/z3.git" CACHE STRING "Z3 repo")
if (CMAKE_BUILD_TYPE STREQUAL "Debug")
  set (Z3_DEBUG "-d")
else()
  set (Z3_DEBUG "")
endif()

ExternalProject_Add(z3
  GIT_REPOSITORY  ${Z3_REPO}
  GIT_TAG ${Z3_TAG}
  BUILD_IN_SOURCE 1
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CONFIGURE_COMMAND env CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER}
	python scripts/mk_make.py --staticlib --prefix=${CMAKE_BINARY_DIR}/run
	BUILD_COMMAND make -j3 -C build
	INSTALL_COMMAND make -C build install
  COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_INSTALL 1
  LOG_BUILD 1)

find_package(Z3 4.5.0)
if (NOT Z3_FOUND)
  ExternalProject_Get_Property (z3 INSTALL_DIR)
  set(Z3_ROOT ${INSTALL_DIR} CACHE PATH "Forced location of Z3" FORCE)
  message(WARNING "No Z3 found. Run \n\tcmake --build . && cmake ${CMAKE_SOURCE_DIR}")
else()
  set_target_properties(z3 PROPERTIES EXCLUDE_FROM_ALL ON)
  include_directories(${Z3_INCLUDE_DIR})
  message ("Found Z3 at ${Z3_EXECUTABLE}")
  # indicate that we want z3 binary to be included in the binary distribution
  install (PROGRAMS ${Z3_EXECUTABLE} DESTINATION bin)
endif()
