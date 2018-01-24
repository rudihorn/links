#!/bin/bash

psql links < music_example.sql
echo GRANT ALL ON public.tracks TO links | psql links
echo GRANT ALL ON public.albums TO links | psql links
../links cds.links --config=links.config
echo "SELECT * FROM albums" | psql links
echo "SELECT * FROM tracks" | psql links
