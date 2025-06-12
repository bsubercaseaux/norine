
# set(Boost_USE_MULTITHREADED ON)
# set(Boost_USE_STATIC_RUNTIME OFF)

set(sources "main.cpp")

find_library(CADICAL_LIBRARY
NAMES cadical
HINTS "${CMAKE_CURRENT_SOURCE_DIR}/../cadical/build/"
)
if (NOT CADICAL_LIBRARY)
	message(FATAL_ERROR "CaDiCaL not found (")
else()
	message("CaDiCaL found at ${CADICAL_LIBRARY}")
endif()
add_library(cadical STATIC IMPORTED GLOBAL)
set_target_properties(cadical PROPERTIES IMPORTED_LOCATION ${CADICAL_LIBRARY})
link_libraries(cadical)

# cross-platform way to elevate the warning level
# -O3 not needed, because it is implied by CMAKE_BUILD_TYPE=Release (which is the default)
if (MSVC)
    # warning level 4
    add_compile_options(/W4)
else()
    # additional warnings
    add_compile_options(-Wall -Wextra -Wpedantic)
endif()

# targets must be added *after* all calls to link_libraries()
add_executable(norine "main.cpp")



