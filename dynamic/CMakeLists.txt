cmake_minimum_required(VERSION 3.12)

project(NORINE VERSION "1.0" LANGUAGES C CXX)

# set(CMAKE_EXE_LINKER_FLAGS "-static")
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake")

if (CMAKE_BUILD_TYPE)
  message("Build type set to ${CMAKE_BUILD_TYPE}.")
else()
  set(CMAKE_BUILD_TYPE Release)
endif ()

add_subdirectory(src)
