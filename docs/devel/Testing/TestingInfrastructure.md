# Infrastructure of Continuous Integration

!!! warning
    Parts of this page are historical: the primary CI nowadays runs as
    GitHub Actions workflows in the KeY repository
    (`.github/workflows/tests.yml` et al.), complemented by a GitLab CI
    configuration. The Docker images and the Jenkins/GitLab runner setup
    described below stem from the earlier infrastructure (note the old
    Java versions mentioned).

## Docker images for testing

We have several Docker images to test KeY. The source files for
building the images are in a Github repository:
<https://github.com/KeYProject/key-test-docker>.

Regulary, the docker images are rebuild on Travis-ci, and published to
Docker Hub.

Our docker images contains a specified version of Java (currently, 8,
11, 16) together with gradle and some SMT-solvers. For specific
version details refer to the repository.


## Setup a CI Runner

In this guide, we explain how to setup a CI runner for Jenkins and
Gitlab-CI. We assume that you have terminal access to the machine.

1. Update the instance
   ```
   $ sudo apt-get update && sudo apt-get upgrade
   ```
2. Install `docker`, `java`
   ```sh
   $ sudo apt-get install docker.io openjdk-11-jre-headless htop
   ```
3. Install the `gitlab-runner`
   ```sh
   $ curl -LJO "https://gitlab-runner-downloads.s3.amazonaws.com/latest/deb/gitlab-runner_amd64.deb"
   $ sudo dpki -i gitlab-runner_amd64.deb
   ```
4. Register the `gitlab-runner`
   ``` 
   $ sudo gitlab-runner register
   ``` 
   Use the information provided on the admin page of your GitLab instance.  
   After this step, the gitlab-ci should work on your computer. Your
   node should be visible on that admin page.

5. Create access for Jenkins: 

     ``` 
     $ sudo adduser jenkins
     $ sudo usermod -aG docker jenkins
     ``` 
   
     The Jenkins controller logins via SSH at the runners. There are
     two options for authentication, password or public/private-key. On
     bwcloud, the password authentication is disabled in
     `/etc/sshd/sshd_config`.

     For simplicity I choose password authentication with very long
     password.

6. Add your runner to
   [Jenkins](http://hudson.se.informatik.tu-darmstadt.de/computer/new)
   using the credentials and IP address of the server.



   
