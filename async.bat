eval "$(ssh-agent -s)"
ssh-add ~/.ssh/secure
git pull visa master
git add ./docs
git commit -m "Update"
git push visa master
pause