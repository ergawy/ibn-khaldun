cmake_minimum_required (VERSION 3.6)

set (PROJ_NAME ibn-khaldun)
project (${PROJ_NAME} VERSION 0.1.0)

include_directories (include)
set (SRCS src/main.c src/cfg.c)

add_executable (${PROJ_NAME} ${SRCS})
