import React from 'react'
import { ContainerRoute, DesignConfig, MenuItem } from './models'
import styles from  './container.module.css';
import SideBar from './components/SideBar'
import Header from './components/Header'
import { useHistory } from 'react-router-dom'

interface ContainerProps {
    children: any
    selectedRoute?: ContainerRoute
    routes?: ContainerRoute[]
    designConfig?: DesignConfig
}

const Container = (props: ContainerProps) => {
    var history = useHistory()
    var sideBarMenu =
        props.designConfig && props.designConfig.sideBarMenu
            ? props.designConfig.sideBarMenu
            : []
    var headerMenu =
        props.designConfig && props.designConfig.headerMenu
            ? props.designConfig.headerMenu
            : []

    const configureMenu = (menu: MenuItem[]) => {
        menu = menu.map((item) => {
            var itemOnClick = item.onClick
            item.onClick = (routeKey?: string) => {
                if (itemOnClick) itemOnClick()
                var route;
                if(routeKey && props.routes){
                    route = props.routes.find(
                        (route) => route.key === routeKey
                    )
                    if (route) {
                        history.push(route.path)
                    }
                    return;
                }

                if (item.routeKey && props.routes) {
                    route = props.routes.find(
                        (route) => route.key === item.routeKey
                    )
                    if (route) {
                        history.push(route.path)
                    }
                }
            }

            if(item.subMenuItemList)
            {
                configureMenu(item.subMenuItemList);
            }

            return item
        })
    }

    configureMenu(sideBarMenu)
    configureMenu(headerMenu)
    return (
        <div className={styles.containerLeftMenu}>
            <div className={styles.header}>
                <Header
                    menu={headerMenu}
                    pageName={props.selectedRoute && props.selectedRoute.label}
                    leftContent={
                        props.designConfig &&
                        props.designConfig.headerLeftContent
                    }
                    rightContent={
                        props.designConfig &&
                        props.designConfig.headerRightContent
                    }
                />
            </div>
            <div className={styles.sidebar}>
                <SideBar
                    headerContent={
                        props.designConfig &&
                        props.designConfig.sideBarHeaderContent
                    }
                    footerContent={
                        props.designConfig &&
                        props.designConfig.sideBarFooterContent
                    }
                    selectedRouteKey={
                        props.selectedRoute && props.selectedRoute.key
                    }
                    menu={sideBarMenu}
                />
            </div>
            <div className={styles.main}>{props.children}</div>
        </div>
    )
}

export default Container
