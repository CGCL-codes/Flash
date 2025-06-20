docker build -t flash .
docker run -itd -v $(pwd)/src:/flash flash